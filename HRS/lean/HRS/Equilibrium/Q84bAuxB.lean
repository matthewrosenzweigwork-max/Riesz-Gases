/-
# HRS.Equilibrium.Q84bAuxB — packet Q84b helpers (derivative of a convolution away from the source)
-/
import HRS.Equilibrium.Q84bAuxA

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-- Derivative of `g * H` at `a`, when `H` vanishes near `a` (`g` the periodic Riesz kernel). -/
theorem q84b_conv_far (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {H : Torus d → ℝ}
    (hH : Integrable H) {a : Torus d} {r : ℝ} (hr : 0 < r)
    (hH0 : ∀ y, ‖a - y‖ < 2 * r → H y = 0) :
    Integrable (fun y => H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (a - y)) : Euc d →L[ℝ] ℝ)) ∧
    HasFDerivAt (Torus.lift (convFun (periodicRiesz d s) H))
      (∫ y, H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (a - y)) : Euc d →L[ℝ] ℝ)) (Torus.rep a) := by
  obtain ⟨Cg, hG⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := HRS.PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨Mg, hMg⟩ := q84b_g_bdd hd hs0 hsd hr
  have hCg0 := hG.hC0
  set M : ℝ := Cg * (r ^ (-s - 1) + 1) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; have := Real.rpow_nonneg hr.le (-s - 1); positivity
  let U : Set (Euc d) := {u | ‖Torus.mk u - a‖ < r}
  have hUo : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Q84a.q84a_continuous_mk.sub continuous_const)) continuous_const
  have hrepU : Torus.rep a ∈ U := by
    show ‖Torus.mk (Torus.rep a) - a‖ < r
    rw [Torus.mk_rep, sub_self, norm_zero]; exact hr
  have hgeo : ∀ u ∈ U, ∀ y, H y ≠ 0 → r ≤ ‖Torus.mk u - y‖ := by
    intro u hu y hy
    have h1 : 2 * r ≤ ‖a - y‖ := by
      by_contra h; exact hy (hH0 y (not_le.1 h))
    have h2 : ‖a - y‖ ≤ ‖Torus.mk u - a‖ + ‖Torus.mk u - y‖ := by
      calc ‖a - y‖ = ‖(a - Torus.mk u) + (Torus.mk u - y)‖ := by congr 1; abel
        _ ≤ ‖a - Torus.mk u‖ + ‖Torus.mk u - y‖ := norm_add_le _ _
        _ = ‖Torus.mk u - a‖ + ‖Torus.mk u - y‖ := by rw [norm_sub_rev (a) (Torus.mk u)]
    have h3 : ‖Torus.mk u - a‖ < r := hu
    linarith
  have hGmeas : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    HRS.KernelGrad.measurable_periodicRieszGrad hsd
  have hmeasF' : ∀ u : Euc d, AEStronglyMeasurable (fun y => H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (Torus.mk u - y)) : Euc d →L[ℝ] ℝ)) := by
    intro u
    refine hH.aestronglyMeasurable.smul ?_
    exact (InnerProductSpace.toDual ℝ (Euc d)).continuous.comp_aestronglyMeasurable
      ((hGmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hbd : ∀ u ∈ U, ∀ y, ‖H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (Torus.mk u - y)) : Euc d →L[ℝ] ℝ)‖ ≤ ‖H y‖ * M := by
    intro u hu y
    by_cases hy : H y = 0
    · simp [hy]
    · rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [LinearIsometryEquiv.norm_map]
      have hr' := hgeo u hu y hy
      have hne : Torus.mk u - y ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hr'; linarith
      refine (hG.bound_norm _ hne).trans ?_
      rw [hM]
      refine mul_le_mul_of_nonneg_left ?_ hCg0
      have := Real.rpow_le_rpow_of_nonpos hr hr' (by linarith : -s - 1 ≤ 0)
      linarith
  have hintF' : Integrable (fun y => H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (a - y)) : Euc d →L[ℝ] ℝ)) := by
    have h0 : a = Torus.mk (Torus.rep a) := (Torus.mk_rep a).symm
    refine Integrable.mono' (hH.norm.mul_const M) ?_ (Eventually.of_forall fun y => ?_)
    · have := hmeasF' (Torus.rep a)
      simpa [Torus.mk_rep] using this
    · have := hbd (Torus.rep a) hrepU y
      simpa [Torus.mk_rep] using this
  refine ⟨hintF', ?_⟩
  have hmeasF : ∀ u : Euc d, AEStronglyMeasurable (fun y => periodicRiesz d s (Torus.mk u - y) * H y) := by
    intro u
    exact (hgi.comp_sub_left (Torus.mk u)).aestronglyMeasurable.mul hH.aestronglyMeasurable
  have hintF : Integrable (fun y => periodicRiesz d s (Torus.mk (Torus.rep a) - y) * H y) := by
    rw [Torus.mk_rep]
    refine Integrable.mono' (hH.norm.mul_const Mg) ?_ (Eventually.of_forall fun y => ?_)
    · simpa [Torus.mk_rep] using hmeasF (Torus.rep a)
    · by_cases hy : H y = 0
      · simp [hy]
      · have h1 : 2 * r ≤ ‖a - y‖ := by
          by_contra h; exact hy (hH0 y (not_le.1 h))
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hMg _ (by linarith)) (abs_nonneg _) |>.trans (le_of_eq (mul_comm _ _))
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (u : Euc d) y => periodicRiesz d s (Torus.mk u - y) * H y)
    (F' := fun (u : Euc d) y => H y • (InnerProductSpace.toDual ℝ (Euc d)
        (periodicRieszGrad d s (Torus.mk u - y)) : Euc d →L[ℝ] ℝ))
    (x₀ := Torus.rep a) (bound := fun y => ‖H y‖ * M) (s := U) (hUo.mem_nhds hrepU)
    (Eventually.of_forall hmeasF) hintF (hmeasF' _)
    (Eventually.of_forall fun y u hu => hbd u hu y) (hH.norm.mul_const M)
    (Eventually.of_forall fun y u hu => ?_)
  · have e : Torus.lift (convFun (periodicRiesz d s) H) =
        fun u => ∫ y, periodicRiesz d s (Torus.mk u - y) * H y := rfl
    rw [e]
    simpa [Torus.mk_rep] using hmain
  · by_cases hy : H y = 0
    · simp only [hy, zero_smul, mul_zero]
      exact hasFDerivAt_const _ _
    · have hr' := hgeo u hu y hy
      have hne : Torus.mk u - y ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hr'; linarith
      have hgr := HRS.KernelGrad.periodicRieszGrad_hasGradientAt hd hs0 hsd hne (u - Torus.rep y)
        (by rw [Q84a.q84a_mk_sub, Torus.mk_rep])
      rw [hasGradientAt_iff_hasFDerivAt] at hgr
      have h1 := hgr.comp u ((hasFDerivAt_id u).sub_const (Torus.rep y))
      have h2 := h1.mul_const (H y)
      have e2 : (fun u' : Euc d => periodicRiesz d s (Torus.mk (u' - Torus.rep y)) * H y) =
          fun u' => periodicRiesz d s (Torus.mk u' - y) * H y := by
        funext u'; rw [Q84a.q84a_mk_sub, Torus.mk_rep]
      simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] at h2
      rw [e2] at h2
      exact h2


/-- The divergence of a vector field given by scalar components. -/
theorem q84b_div_eq {w : Fin d → Torus d → ℝ} {a : Torus d}
    (hdiff : ∀ j, DifferentiableAt ℝ (Torus.lift (w j)) (Torus.rep a)) :
    Torus.div (fun z => (WithLp.toLp 2 fun j => w j z : Euc d)) a =
      ∑ j, Torus.partialDeriv j (w j) a := by
  unfold Torus.div
  set v : Torus d → Euc d := fun z => (WithLp.toLp 2 fun j => w j z : Euc d) with hv
  have hcomp : ∀ j y, Torus.lift v y j = Torus.lift (w j) y := fun j y => rfl
  have hdiff' : DifferentiableAt ℝ (Torus.lift v) (Torus.rep a) := by
    rw [differentiableAt_euclidean]
    intro j
    have : (fun y => Torus.lift v y j) = Torus.lift (w j) := funext (hcomp j)
    rw [this]
    exact hdiff j
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : HasFDerivAt (fun y => Torus.lift v y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (fderiv ℝ (Torus.lift v) (Torus.rep a))) (Torus.rep a) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp _ hdiff'.hasFDerivAt
  have h2 := h1.fderiv
  have h3 : (fun y => Torus.lift v y i) = Torus.lift (w i) := funext (hcomp i)
  rw [h3] at h2
  have h4 : Torus.partialDeriv i (w i) a =
      fderiv ℝ (Torus.lift (w i)) (Torus.rep a) (EuclideanSpace.single i 1) := rfl
  rw [h4, h2]
  simp

theorem q84b_partialDeriv_congr {f f' : Torus d → ℝ} {y : Torus d} (h : f =ᶠ[𝓝 y] f')
    (j : Fin d) : Torus.partialDeriv j f y = Torus.partialDeriv j f' y := by
  unfold Torus.partialDeriv
  have hm : Tendsto (Torus.mk : Euc d → Torus d) (𝓝 (Torus.rep y)) (𝓝 y) := by
    have := Q84a.q84a_continuous_mk.tendsto (Torus.rep y)
    rwa [Torus.mk_rep] at this
  have : Torus.lift f =ᶠ[𝓝 (Torus.rep y)] Torus.lift f' := hm.eventually h
  rw [this.fderiv_eq]

theorem q84b_mul_smooth {χ f : Torus d → ℝ} {b : Torus d} (hχ : Torus.IsSmooth χ)
    (hχb : ∀ᶠ z in 𝓝 b, χ z = 0)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) {u : Euc d | Torus.mk u ≠ b}) :
    Torus.IsSmooth (fun z => χ z * f z) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_iff_contDiffAt]
  intro u
  have hU : IsOpen {u : Euc d | Torus.mk u ≠ b} :=
    (isOpen_compl_singleton (x := b)).preimage Q84a.q84a_continuous_mk
  by_cases hu : Torus.mk u = b
  · have hm : Tendsto (Torus.mk : Euc d → Torus d) (𝓝 u) (𝓝 b) := by
      have h : Tendsto (Torus.mk : Euc d → Torus d) (𝓝 u) (𝓝 (Torus.mk u)) :=
        Q84a.q84a_continuous_mk.tendsto u
      rwa [hu] at h
    have hev : Torus.lift (fun z => χ z * f z) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [hm.eventually hχb] with v hv
      simp [Torus.lift, hv]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) u :=
      hf.contDiffAt (hU.mem_nhds hu)
    exact (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift χ) from hχ).contDiffAt.mul h1

end HRS.Q84b
