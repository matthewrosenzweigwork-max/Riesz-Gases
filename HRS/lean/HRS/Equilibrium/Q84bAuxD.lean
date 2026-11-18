/-
# HRS.Equilibrium.Q84bAuxD — packet Q84b: local cancellation formula for `Jop`
-/
import HRS.Equilibrium.Q84bAuxC

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-- Integrand of the cancellation form of `∫ ∇g(a - y)·ξ(y) dy` after the substitution `z = a - y`. -/
def q84b_pvU (G : Torus d → Euc d) (ξ : Torus d → Euc d) (a z : Torus d) : ℝ :=
  inner ℝ (G z) (if ‖z‖ ≤ 1 / 4 then ξ (a - z) - ξ a else ξ (a - z))

theorem q84b_Jop_local (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {f : Torus d → ℝ} {a b : Torus d} (hab : a ≠ b)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) {u : Euc d | Torus.mk u ≠ b})
    (hint : Integrable (fun z => ‖Torus.grad f z‖)) :
    Integrable (q84b_pvU (periodicRieszGrad d s) (fun y => ρ y • Torus.grad f y) a) ∧
    Jop d s ρ f a = ∫ z, q84b_pvU (periodicRieszGrad d s) (fun y => ρ y • Torus.grad f y) a z := by
  have hgi : Integrable (periodicRiesz d s) := HRS.PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨Cg, hGood⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  set H : Fin d → Torus d → ℝ := fun j y => ρ y * Torus.partialDeriv j f y with hH
  have hpd_meas : ∀ j, Measurable (Torus.partialDeriv j f) := by
    intro j
    unfold Torus.partialDeriv
    exact (measurable_fderiv_apply_const ℝ (Torus.lift f) (EuclideanSpace.single j 1)).comp
      (q84b_measurable_rep d)
  have hHint : ∀ j, Integrable (H j) := by
    intro j
    refine Integrable.mono' (hint.const_mul Bρ) ((hρc.measurable.mul (hpd_meas j)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    have h1 : |Torus.partialDeriv j f y| ≤ ‖Torus.grad f y‖ := by
      have := PiLp.norm_apply_le (Torus.grad f y) j
      rwa [Real.norm_eq_abs, HRS.PDE.MFAux.grad_apply] at this
    simp only [hH, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hBρ y) h1 (abs_nonneg _) hBρ0
  obtain ⟨χ, hχs, hχa, hχb⟩ := q84b_exists_cutoff hab
  set f1 : Torus d → ℝ := fun z => χ z * f z with hf1def
  have hf1 : Torus.IsSmooth f1 := q84b_mul_smooth hχs hχb hsm
  have hf1C2 : Torus.IsCk 2 f1 := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f1) := hf1
    exact h.of_le (by norm_cast)
  set H1 : Fin d → Torus d → ℝ := fun j y => ρ y * Torus.partialDeriv j f1 y with hH1def
  have hH1 : ∀ j, Torus.IsCk 1 (H1 j) := fun j =>
    HRS.PDE.MFAux.isCk_mul_partialDeriv ρ f1 hρ1 hf1C2 j
  have hH1c : ∀ j, Continuous (H1 j) := fun j => HRS.PDE.MFAux.continuous_of_isCk (hH1 j)
  set H2 : Fin d → Torus d → ℝ := fun j y => H j y - H1 j y with hH2def
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff.1 hχa
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hH20 : ∀ j y, ‖a - y‖ < 2 * r → H2 j y = 0 := by
    intro j y hy
    have hy' : dist y a < ε := by
      rw [dist_eq_norm, norm_sub_rev]; rw [hrdef] at hy; linarith
    have hev : f1 =ᶠ[𝓝 y] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball a ε from by
        rw [Metric.mem_ball]; exact hy')] with z hz
      have := hεa (show dist z a < ε from hz)
      simp [hf1def, this]
    have := q84b_partialDeriv_congr hev j
    simp only [hH2def, hH, hH1def, this, sub_self]
  have hH2int : ∀ j, Integrable (H2 j) := fun j =>
    (hHint j).sub ((hH1c j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hsplit := fun j => q84b_conv_split hd hs0 hsd (H := H j) (H1 := H1 j) (H2 := H2 j)
    (hH1 j) (hH2int j) (fun y => by simp [hH2def]) hr (hH20 j) j
  -- the divergence
  have hJ : Jop d s ρ f a = ∑ j, Torus.partialDeriv j (convFun (periodicRiesz d s) (H j)) a := by
    unfold Jop
    exact q84b_div_eq (fun j => (hsplit j).1)
  have hpart : ∀ j, Torus.partialDeriv j (convFun (periodicRiesz d s) (H j)) a =
      convFun (periodicRiesz d s) (Torus.partialDeriv j (H1 j)) a +
        ∫ y, H2 j y * (periodicRieszGrad d s (a - y)) j := fun j => (hsplit j).2
  have hdc : ∀ j, Continuous (Torus.partialDeriv j (H1 j)) := fun j =>
    HRS.PDE.continuous_partialDeriv j _ (hH1 j)
  -- Part 1: the smooth part, through the cancellation convention
  have hP1 : ∑ j, convFun (periodicRiesz d s) (Torus.partialDeriv j (H1 j)) a =
      ∑ j, (convGradConv (periodicRieszGrad d s) (H1 j) a).ofLp j := by
    rw [HRS.PDE.MFAux.sum_convGradConv_eq hd s hs0 hsd H1 hH1 a]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun y => periodicRiesz d s (a - y) *
        Torus.partialDeriv j (H1 j) y) := by
      intro j _
      obtain ⟨B, hB⟩ := q84b_exists_bound_of_cont (hdc j)
      exact (hgi.comp_sub_left a).mul_bdd (c := B) (hdc j).aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa using hB y)
    unfold convFun
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ hint]
  have hK : ∀ j, Integrable (HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a) := by
    intro j
    obtain ⟨B, hB0, hB⟩ := HRS.KernelGrad.isCk_bounded (hH1 j)
    obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.isLipschitz_of_isCk (hH1 j)
    exact HRS.KernelGrad.integrable_kern hGood (hH1c j).measurable hB hL hL0 hB0 a
  have hKj : ∀ j, Integrable (fun z => (HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j) :=
    fun j => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (hK j)
  have hconv : ∀ j, (convGradConv (periodicRieszGrad d s) (H1 j) a).ofLp j =
      ∫ z, (HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j := by
    intro j
    rw [HRS.KernelGrad.convGradConv_eq_integral_kern]
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm (hK j)
    simpa using this.symm
  -- Part 2: the far part
  have hT2 : ∀ j, Integrable (fun z => H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) := by
    intro j
    obtain ⟨hi, -⟩ := q84b_conv_far hd hs0 hsd (hH2int j) hr (hH20 j)
    have h1 := hi.comp_sub_left a
    have h2 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).integrable_comp h1
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp [sub_sub_cancel, InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
  have hI2 : ∀ j, ∫ z, H2 j (a - z) * (periodicRieszGrad d s z).ofLp j =
      ∫ y, H2 j y * (periodicRieszGrad d s (a - y)).ofLp j := by
    intro j
    have := integral_sub_left_eq_self (fun y => H2 j y * (periodicRieszGrad d s (a - y)).ofLp j)
      volume a
    simpa [sub_sub_cancel] using this
  -- pointwise identification
  have hpt : ∀ z, ∑ j, ((HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j +
      H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) =
      q84b_pvU (periodicRieszGrad d s) (fun y => ρ y • Torus.grad f y) a z := by
    intro z
    unfold q84b_pvU
    rw [HRS.KernelGrad.inner_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hxi : ∀ y, (ρ y • Torus.grad f y).ofLp j = H j y := by
      intro y; simp [hH, HRS.PDE.MFAux.grad_apply]
    have hH2a : H2 j a = 0 := hH20 j a (by rw [sub_self, norm_zero]; linarith)
    have hH1a : H1 j a = H j a := by
      have : H j a - H1 j a = 0 := hH2a
      linarith
    unfold HRS.KernelGrad.kern
    split_ifs with h
    · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply, hxi, hH1a, hH2def]
      ring
    · simp only [PiLp.smul_apply, smul_eq_mul, hxi, hH2def]
      ring
  have hsumInt : Integrable (fun z => ∑ j, ((HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j +
      H2 j (a - z) * (periodicRieszGrad d s z).ofLp j)) :=
    integrable_finsetSum _ fun j _ => (hKj j).add (hT2 j)
  have hJeq : Jop d s ρ f a = ∫ z, ∑ j, ((HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j +
      H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) := by
    have hsw : ∫ z, ∑ j, ((HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j +
        H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) =
        ∑ j, ((∫ z, (HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j) +
          ∫ z, H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) := by
      have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin d)), Integrable (fun z =>
          (HRS.KernelGrad.kern (periodicRieszGrad d s) (H1 j) a z).ofLp j +
            H2 j (a - z) * (periodicRieszGrad d s z).ofLp j) := fun j _ => (hKj j).add (hT2 j)
      rw [integral_finsetSum _ hint2]
      exact Finset.sum_congr rfl fun j _ => integral_add (hKj j) (hT2 j)
    rw [hsw, Finset.sum_add_distrib, hJ]
    calc ∑ j, Torus.partialDeriv j (convFun (periodicRiesz d s) (H j)) a
        = ∑ j, (convFun (periodicRiesz d s) (Torus.partialDeriv j (H1 j)) a +
          ∫ y, H2 j y * (periodicRieszGrad d s (a - y)).ofLp j) :=
          Finset.sum_congr rfl fun j _ => hpart j
      _ = ∑ j, convFun (periodicRiesz d s) (Torus.partialDeriv j (H1 j)) a +
          ∑ j, ∫ y, H2 j y * (periodicRieszGrad d s (a - y)).ofLp j := Finset.sum_add_distrib
      _ = _ := by
        rw [hP1]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => hconv j
        · exact Finset.sum_congr rfl fun j _ => (hI2 j).symm
  refine ⟨?_, ?_⟩
  · simpa only [hpt] using hsumInt
  · rw [hJeq]; exact integral_congr_ae (Eventually.of_forall hpt)

end HRS.Q84b
