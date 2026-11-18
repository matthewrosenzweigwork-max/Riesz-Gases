import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16S) Nl1: convolution calculus for the weak form of the nonlocal term (P6, part 1)

For a locally integrable kernel `κ` and `u` of class `C^1` with compact support:
`sa16sp_convFun_fderiv` (differentiability of `κ ⋆ u` and `∂_v (κ ⋆ u) = κ ⋆ ∂_v u`), `sa16sp_convFun_cont`,
`sa16sp_swap` (`∫ w (κ ⋆ f) = ∫ f (κ ⋆ w)` for even `κ`, `f, w` continuous with compact support, Fubini),
`sa16sp_ibp_C1` (integration by parts against a `C_c^∞` function for a differentiable function with continuous
directional derivative), `sa16sp_gradient_apply`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nl1
variable {d : ℕ}

lemma sa16sp_gradient_apply (f : Euc d → ℝ) (x : Euc d) (k : Fin d) :
    gradient f x k = fderiv ℝ f x (EuclideanSpace.single k 1) := by
  have h := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := EuclideanSpace.single k 1)
  rw [EuclideanSpace.inner_single_right] at h
  simpa using h

lemma sa16sp_convFun_eq (κ u : Euc d → ℝ) (x : Euc d) :
    convFun κ u x = ∫ z, κ z * u (x - z) := by
  have h := integral_sub_left_eq_self (fun z => κ z * u (x - z)) (volume : Measure (Euc d)) x
  unfold convFun
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]

lemma sa16sp_convFun_eq_conv (κ u : Euc d → ℝ) :
    convFun κ u = convolution κ u (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [sa16sp_convFun_eq]
  simp [convolution, smul_eq_mul]

lemma sa16sp_convFun_cont {κ : Euc d → ℝ} (hκ : LocallyIntegrable κ volume) {u : Euc d → ℝ}
    (hu : Continuous u) (hus : HasCompactSupport u) : Continuous (convFun κ u) := by
  rw [sa16sp_convFun_eq_conv]
  exact hus.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hu

lemma sa16sp_convFun_fderiv {κ : Euc d → ℝ} (hκ : LocallyIntegrable κ volume) {u : Euc d → ℝ}
    (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u) (x : Euc d) :
    DifferentiableAt ℝ (convFun κ u) x ∧
      ∀ v, fderiv ℝ (convFun κ u) x v = convFun κ (fun y => fderiv ℝ u y v) x := by
  have h1 := hus.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hu x
  rw [← sa16sp_convFun_eq_conv] at h1
  refine ⟨h1.differentiableAt, fun v => ?_⟩
  rw [h1.fderiv]
  have hc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ u) := hus.fderiv ℝ
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hκ hcs hc x v,
    ← sa16sp_convFun_eq_conv]

lemma sa16sp_swap {κ f w : Euc d → ℝ} (hκ : LocallyIntegrable κ volume) (hκe : ∀ z, κ (-z) = κ z)
    (hf : Continuous f) (hfs : HasCompactSupport f) (hw : Continuous w) (hws : HasCompactSupport w) :
    ∫ x, w x * convFun κ f x = ∫ y, f y * convFun κ w y := by
  obtain ⟨Rf, hRf0, hRf⟩ := sa16r_cc_support hfs
  obtain ⟨Rw, hRw0, hRw⟩ := sa16r_cc_support hws
  set R : ℝ := Rf + Rw with hR
  have hnorm : ∀ x y, w x ≠ 0 → f y ≠ 0 → ‖x - y‖ ≤ R := by
    intro x y hx hy
    have h1 : ‖x‖ ≤ Rw := by by_contra h; exact hx (hRw x (not_le.1 h))
    have h2 : ‖y‖ ≤ Rf := by by_contra h; exact hy (hRf y (not_le.1 h))
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ R := by rw [hR]; linarith
  set κR : Euc d → ℝ := (closedBall (0 : Euc d) R).indicator κ with hκR
  have hκRi : Integrable κR :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (hκ.integrableOn_isCompact (isCompact_closedBall _ _))
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfs
  have hI : Integrable (fun p : Euc d × Euc d => f p.2 * κR (p.1 - p.2)) (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfi hκRi
      (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    simpa [smul_eq_mul] using this
  obtain ⟨Bw, hBw⟩ := hw.bounded_above_of_compact_support hws
  have hG : Integrable (fun p : Euc d × Euc d => w p.1 * (f p.2 * κR (p.1 - p.2))) (volume.prod volume) :=
    hI.bdd_mul (hw.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hBw p.1)
  have hpt : ∀ x y, w x * (κ (x - y) * f y) = w x * (f y * κR (x - y)) := by
    intro x y
    by_cases h1 : w x = 0
    · simp [h1]
    by_cases h2 : f y = 0
    · simp [h2]
    have : x - y ∈ closedBall (0 : Euc d) R := by simpa using hnorm x y h1 h2
    rw [hκR, Set.indicator_of_mem this]; ring
  have hpt2 : ∀ y x, f y * (κ (y - x) * w x) = w x * (f y * κR (x - y)) := by
    intro y x
    by_cases h1 : w x = 0
    · simp [h1]
    by_cases h2 : f y = 0
    · simp [h2]
    have : x - y ∈ closedBall (0 : Euc d) R := by simpa using hnorm x y h1 h2
    rw [hκR, Set.indicator_of_mem this, show y - x = -(x - y) by abel, hκe]; ring
  have hL : ∫ x, w x * convFun κ f x = ∫ x, ∫ y, w x * (f y * κR (x - y)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show w x * ∫ y, κ (x - y) * f y = _
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => hpt x y)
  have hRr : ∫ y, f y * convFun κ w y = ∫ y, ∫ x, w x * (f y * κR (x - y)) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show f y * ∫ x, κ (y - x) * w x = _
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => hpt2 y x)
  rw [hL, hRr]
  exact integral_integral_swap hG

/-- integration by parts for a differentiable function with continuous directional derivative -/
lemma sa16sp_ibp_C1 {H ψ : Euc d → ℝ} (hH : Differentiable ℝ H) (e : Euc d)
    (hHd : Continuous (fun x => fderiv ℝ H x e)) (hψ : IsCcInfty ψ) :
    ∫ x, ψ x * fderiv ℝ H x e = -∫ x, fderiv ℝ ψ x e * H x := by
  have hdψ := sa16s_cc_fderiv hψ e
  have hHc : Continuous H := hH.continuous
  have h1 : Integrable (fun x => fderiv ℝ ψ x e * H x) :=
    (hdψ.1.continuous.mul hHc).integrable_of_hasCompactSupport hdψ.2.mul_right
  have h2 : Integrable (fun x => ψ x * fderiv ℝ H x e) :=
    (hψ.1.continuous.mul hHd).integrable_of_hasCompactSupport hψ.2.mul_right
  have h3 : Integrable (fun x => ψ x * H x) :=
    (hψ.1.continuous.mul hHc).integrable_of_hasCompactSupport hψ.2.mul_right
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e) h1 h2 h3
    (fun x _ => (hψ.1.differentiable (by simp)) x) (fun x _ => hH x)
  linarith

end Nl1

end HRS.Whole.AppendixA.Phase2SA16R
