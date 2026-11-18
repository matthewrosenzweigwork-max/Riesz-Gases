/-
# HRS.Equilibrium.Q84bAuxA — packet Q84b helpers (cutoffs on the torus, convolution derivatives)
-/
import HRS.Equilibrium.Q84aAuxC
import HRS.Equilibrium.Q84aAuxB
import HRS.PDE.MeanFieldAux

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-! ### A smooth cutoff on the torus: `1` near `a`, `0` near `b`. -/

theorem q84b_cosMode_zero (k : Lattice d) : Torus.cosMode k (0 : Torus d) = 1 := by
  have h : (0 : Torus d) = Torus.mk (0 : Euc d) := by
    funext i; simp [Torus.mk]
  rw [h, Torus.cosMode_mk]
  simp [Lattice.dot]

theorem q84b_exists_coord {a b : Torus d} (hab : a ≠ b) :
    ∃ i : Fin d, Torus.cosMode (Pi.single i (1 : ℤ) : Lattice d) (b - a) < 1 := by
  by_contra hcon
  push Not at hcon
  apply hab
  funext i
  have h1 := hcon i
  have h2 : Torus.cosMode (Pi.single i (1 : ℤ) : Lattice d) (b - a) ≤ 1 := by
    have := Torus.norm_cosMode_le (Pi.single i (1 : ℤ) : Lattice d) (b - a)
    exact (le_abs_self _).trans (by simpa using this)
  have h3 : Torus.cosMode (Pi.single i (1 : ℤ) : Lattice d) (b - a) = 1 := le_antisymm h2 h1
  have hm : Torus.mk (Torus.rep (b - a)) = b - a := Torus.mk_rep _
  rw [← hm, Torus.cosMode_mk] at h3
  have h4 : Lattice.dot (Pi.single i (1 : ℤ) : Lattice d) (Torus.rep (b - a)) = Torus.rep (b - a) i := by
    simp [Lattice.dot, Pi.single_apply]
  rw [h4, Real.cos_eq_one_iff] at h3
  obtain ⟨n, hn⟩ := h3
  have h5 : Torus.rep (b - a) i = n := by
    have hpi := Real.pi_pos
    nlinarith
  have h6 : (b - a) i = 0 := by
    have := congrFun hm i
    rw [← this]
    simp only [Torus.mk, h5]
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩
  have : b i - a i = 0 := by simpa using h6
  exact (sub_eq_zero.1 this).symm


/-- The one-variable factors of the cutoff. -/
def q84b_cutFac (a : Torus d) (τ₁ τ₂ : ℝ) (j : Fin d) (z : Torus d) : ℝ :=
  Real.smoothTransition
    ((Torus.cosMode (Pi.single j (1 : ℤ) : Lattice d) (z - a) - τ₂) / (τ₁ - τ₂))

def q84b_cut (a : Torus d) (τ₁ τ₂ : ℝ) (z : Torus d) : ℝ := ∏ j, q84b_cutFac a τ₁ τ₂ j z

theorem q84b_continuous_cosCoord (a : Torus d) (j : Fin d) :
    Continuous fun z : Torus d => Torus.cosMode (Pi.single j (1 : ℤ) : Lattice d) (z - a) :=
  (Torus.continuous_cosMode _).comp (continuous_id.sub continuous_const)

theorem q84b_cut_smooth (a : Torus d) (τ₁ τ₂ : ℝ) : Torus.IsSmooth (q84b_cut a τ₁ τ₂) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hlift : Torus.lift (q84b_cut a τ₁ τ₂) = fun u : Euc d => ∏ j : Fin d,
      Real.smoothTransition ((Real.cos (2 * Real.pi * (u j - Torus.rep a j)) - τ₂) / (τ₁ - τ₂)) := by
    funext u
    simp only [Torus.lift, Function.comp, q84b_cut, q84b_cutFac]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hm : Torus.mk (u - Torus.rep a) = Torus.mk u - a := by
      rw [Q84a.q84a_mk_sub, Torus.mk_rep]
    rw [← hm, Torus.cosMode_mk]
    simp [Lattice.dot, Pi.single_apply]
  rw [hlift]
  refine contDiff_prod fun j _ => ?_
  refine Real.smoothTransition.contDiff.comp ?_
  refine ContDiff.div_const (ContDiff.sub ?_ contDiff_const) _
  refine Real.contDiff_cos.comp ?_
  exact contDiff_const.mul ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.sub contDiff_const)

theorem q84b_exists_cutoff {a b : Torus d} (hab : a ≠ b) :
    ∃ χ : Torus d → ℝ, Torus.IsSmooth χ ∧ (∀ᶠ z in 𝓝 a, χ z = 1) ∧ (∀ᶠ z in 𝓝 b, χ z = 0) := by
  obtain ⟨i, hi⟩ := q84b_exists_coord hab
  set κ := Torus.cosMode (Pi.single i (1 : ℤ) : Lattice d) (b - a) with hκ
  set τ₂ := κ + (1 - κ) / 3 with hτ₂
  set τ₁ := κ + 2 * (1 - κ) / 3 with hτ₁
  have h1 : τ₂ < τ₁ := by rw [hτ₂, hτ₁]; linarith
  have h2 : τ₁ < 1 := by rw [hτ₁]; linarith
  have h3 : κ < τ₂ := by rw [hτ₂]; linarith
  refine ⟨q84b_cut a τ₁ τ₂, q84b_cut_smooth a τ₁ τ₂, ?_, ?_⟩
  · -- near `a` every factor is `1`
    have hall : ∀ j : Fin d, ∀ᶠ z in 𝓝 a,
        1 ≤ (Torus.cosMode (Pi.single j (1 : ℤ) : Lattice d) (z - a) - τ₂) / (τ₁ - τ₂) := by
      intro j
      have hc := (q84b_continuous_cosCoord a j).continuousAt (x := a)
      have hv : Torus.cosMode (Pi.single j (1 : ℤ) : Lattice d) (a - a) = 1 := by
        rw [sub_self]; exact q84b_cosMode_zero _
      have hlt : τ₁ < Torus.cosMode (Pi.single j (1 : ℤ) : Lattice d) (a - a) := by rw [hv]; exact h2
      filter_upwards [hc.eventually (lt_mem_nhds hlt)] with z hz
      rw [le_div_iff₀ (by linarith)]
      linarith
    have := (eventually_all.2 hall)
    filter_upwards [this] with z hz
    unfold q84b_cut q84b_cutFac
    refine Finset.prod_eq_one fun j _ => ?_
    exact Real.smoothTransition.eq_one_iff_one_le.2 (hz j)
  · have hc := (q84b_continuous_cosCoord a i).continuousAt (x := b)
    have hlt : Torus.cosMode (Pi.single i (1 : ℤ) : Lattice d) (b - a) < τ₂ := h3
    filter_upwards [hc.eventually (gt_mem_nhds hlt)] with z hz
    unfold q84b_cut
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    unfold q84b_cutFac
    refine Real.smoothTransition.zero_iff_nonpos.2 ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)


/-! ### Convolution with a `C¹` function (copied from `MeanFieldSchauder`, which is not built here) -/

theorem q84b_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem q84b_convFun_eq' (g h : Torus d → ℝ) (x : Torus d) :
    convFun g h x = ∫ z, g z * h (x - z) := by
  unfold convFun
  rw [← integral_sub_left_eq_self (fun y => g (x - y) * h y) volume x]
  simp

theorem q84b_exists_bound_of_cont {h : Torus d → ℝ} (hc : Continuous h) :
    ∃ B : ℝ, ∀ w, |h w| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun w => by simpa using hB w (Set.mem_univ w)⟩

theorem q84b_convFun_hasFDerivAt {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h)
    (v : Euc d) :
    HasFDerivAt (Torus.lift (convFun g h))
      (∫ z, g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) v := by
  obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.norm_fderiv_le_of_isCk hh
  have hH : ContDiff ℝ 1 (Torus.lift h) := hh
  have hHd : Differentiable ℝ (Torus.lift h) := hH.differentiable one_ne_zero
  have hHc : Continuous (Torus.lift h) := hH.continuous
  have hHc' : Continuous (fderiv ℝ (Torus.lift h)) := hH.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := q84b_exists_bound_of_cont (HRS.PDE.MFAux.continuous_of_isCk hh)
  have e : Torus.lift (convFun g h) = fun w => ∫ z, g z * Torus.lift h (w - Torus.rep z) := by
    funext w
    simp only [Torus.lift, Function.comp]
    rw [q84b_convFun_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [HRS.KernelGrad.mk_sub, Torus.mk_rep]
  rw [e]
  have hrep := q84b_measurable_rep d
  have hmeas : ∀ w, AEStronglyMeasurable (fun z : Torus d => g z * Torus.lift h (w - Torus.rep z)) := by
    intro w
    exact hg.aestronglyMeasurable.mul
      (hHc.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
  have hint : Integrable (fun z : Torus d => g z * Torus.lift h (v - Torus.rep z)) := by
    refine hg.mul_bdd (c := B) (hHc.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have := hB (Torus.mk (v - Torus.rep z))
    simpa [Torus.lift] using this
  have hmeas' : AEStronglyMeasurable (fun z : Torus d => g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) := by
    exact hg.aestronglyMeasurable.smul
      (hHc'.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun w z => g z * Torus.lift h (w - Torus.rep z))
    (F' := fun w z => g z • fderiv ℝ (Torus.lift h) (w - Torus.rep z)) (bound := fun z => ‖g z‖ * L)
    (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hmeas'
    (Filter.Eventually.of_forall fun z w _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _))
    (hg.norm.mul_const L)
    (Filter.Eventually.of_forall fun z w _ => by
      have h1 := (hHd (w - Torus.rep z)).hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const (Torus.rep z))
      have h2 := h1.const_mul (g z)
      simpa using h2)

theorem q84b_convFun_fderiv_integrable {g h : Torus d → ℝ} (hg : Integrable g)
    (hh : Torus.IsCk 1 h) (v : Euc d) :
    Integrable (fun z => g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) := by
  obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.norm_fderiv_le_of_isCk hh
  have hH : ContDiff ℝ 1 (Torus.lift h) := hh
  have hHc' : Continuous (fderiv ℝ (Torus.lift h)) := hH.continuous_fderiv one_ne_zero
  have hrep := q84b_measurable_rep d
  refine Integrable.mono' (hg.norm.mul_const L) (hg.aestronglyMeasurable.smul
      (hHc'.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)

theorem q84b_convFun_partialDeriv {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h)
    (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (convFun g h) x = convFun g (Torus.partialDeriv j h) x := by
  have hd := q84b_convFun_hasFDerivAt hg hh (Torus.rep x)
  have e0 : Torus.partialDeriv j (convFun g h) x =
      fderiv ℝ (Torus.lift (convFun g h)) (Torus.rep x) (EuclideanSpace.single j 1) := rfl
  rw [e0, hd.fderiv, ContinuousLinearMap.integral_apply (q84b_convFun_fderiv_integrable hg hh _),
    q84b_convFun_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_apply, smul_eq_mul]
  congr 1
  rw [← HRS.PDE.partialDeriv_mk j h hh, HRS.KernelGrad.mk_sub, Torus.mk_rep, Torus.mk_rep]


/-! ### Boundedness of `g` away from the origin and of the gradient -/

theorem q84b_g_continuousAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (periodicRiesz d s) z := by
  have hq := (HRS.KernelGrad.isOpenQuotientMap_mk (d := d))
  have hcd := HRS.KernelGrad.contDiffOn_periodicRiesz hd hs0 hsd (s := s)
  have hU : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
    (isOpen_compl_singleton (x := (0 : Torus d))).preimage hq.continuous
  have hmk : Torus.mk (Torus.rep z) = z := Torus.mk_rep z
  have h1 : ContinuousAt (fun y : Euc d => periodicRiesz d s (Torus.mk y)) (Torus.rep z) :=
    (hcd.continuousOn.continuousAt (hU.mem_nhds (show Torus.mk (Torus.rep z) ≠ 0 by rw [hmk]; exact hz)))
  have := (hq.continuousAt_comp_iff (g := periodicRiesz d s) (x := Torus.rep z)).1 h1
  rwa [hmk] at this

theorem q84b_g_bdd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ u : Torus d, r ≤ ‖u‖ → |periodicRiesz d s u| ≤ M := by
  have hK : IsCompact {u : Torus d | r ≤ ‖u‖} :=
    (isClosed_le continuous_const continuous_norm).isCompact
  have hc : ContinuousOn (periodicRiesz d s) {u : Torus d | r ≤ ‖u‖} := fun u hu =>
    (q84b_g_continuousAt hd hs0 hsd (by
      intro h0; rw [h0] at hu; exact absurd (show r ≤ ‖(0 : Torus d)‖ from hu) (by rw [norm_zero]; exact not_le.2 hr))).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨M, fun u hu => by simpa using hM u hu⟩

end HRS.Q84b
