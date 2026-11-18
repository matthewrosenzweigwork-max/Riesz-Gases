import HRS.MS.SuppU2Aux4

/-!
# U2 auxiliary 5: differentiation of `u2Conv κ g` with the derivatives on the kernel

For `g` continuous, supported in `closedBall 0 r`, and `‖x0‖ ≥ 2 r`, the iterated derivatives of
`x ↦ ∫ κ(z) g(x-z) dz` on the ball `ball x0 (r/2)` are `∫ g(y) D^j κ(x - y) dy`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_integrable_of_support {g : Euc d → ℝ} (hg : Continuous g) {r : ℝ}
    (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0) : Integrable g volume := by
  refine hg.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) r) ?_
  intro y hy
  by_contra hy'
  apply hy
  exact hsupp y (by simpa using hy')

lemma u2_meas_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (T : Euc d → F)
    {g : Euc d → ℝ} (hg : Continuous g) {r : ℝ} (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0)
    (x' : Euc d) (hT : ∀ y : Euc d, ‖y‖ ≤ r → ContinuousAt T (x' - y)) :
    AEStronglyMeasurable (fun y => g y • T (x' - y)) volume := by
  have hind : (fun y => g y • T (x' - y)) =
      (closedBall (0 : Euc d) r).indicator (fun y => g y • T (x' - y)) := by
    funext y
    by_cases hy : y ∈ closedBall (0 : Euc d) r
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have : r < ‖y‖ := by simpa using hy
      rw [hsupp y this, zero_smul]
  rw [hind, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_closedBall
  intro y hy
  have hy' : ‖y‖ ≤ r := by simpa using hy
  have h1 : ContinuousAt (fun y : Euc d => T (x' - y)) y :=
    ContinuousAt.comp (g := T) (f := fun y : Euc d => x' - y) (hT y hy')
      (continuousAt_const.sub continuousAt_id)
  exact (hg.continuousAt.smul h1).continuousWithinAt

lemma u2_ks_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : Euc d → F) {r : ℝ} (hr : 0 < r) {g : Euc d → ℝ} (hg : Continuous g)
    (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0) {x0 : Euc d} (hx0 : 2 * r ≤ ‖x0‖)
    (hDd : ∀ z : Euc d, r / 2 ≤ ‖z‖ → DifferentiableAt ℝ D z)
    (hD'c : ∀ z : Euc d, r / 2 ≤ ‖z‖ → ContinuousAt (fderiv ℝ D) z)
    {B0 B1 : ℝ} (hB0 : ∀ z : Euc d, r / 2 ≤ ‖z‖ → ‖D z‖ ≤ B0)
    (hB1 : ∀ z : Euc d, r / 2 ≤ ‖z‖ → ‖fderiv ℝ D z‖ ≤ B1)
    {x : Euc d} (hx : x ∈ ball x0 (r / 2)) :
    HasFDerivAt (fun x' => ∫ y, g y • D (x' - y)) (∫ y, g y • fderiv ℝ D (x - y)) x := by
  have hgi : Integrable g volume := u2_integrable_of_support hg hsupp
  -- far from the origin on the support
  have hfar : ∀ x' ∈ ball x0 (r / 2), ∀ y : Euc d, ‖y‖ ≤ r → r / 2 ≤ ‖x' - y‖ := by
    intro x' hx' y hy
    have h1 : ‖x' - x0‖ < r / 2 := mem_ball_iff_norm.mp hx'
    have h2 : ‖x0‖ ≤ ‖x'‖ + ‖x' - x0‖ := by
      calc ‖x0‖ = ‖x' - (x' - x0)‖ := by simp
        _ ≤ ‖x'‖ + ‖x' - x0‖ := norm_sub_le _ _
    have h3 : ‖x'‖ ≤ ‖x' - y‖ + ‖y‖ := by
      calc ‖x'‖ = ‖(x' - y) + y‖ := by simp
        _ ≤ _ := norm_add_le _ _
    linarith
  have hUx : ball x0 (r / 2) ∈ 𝓝 x := IsOpen.mem_nhds isOpen_ball hx
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x' y => g y • D (x' - y)) (F' := fun x' y => g y • fderiv ℝ D (x' - y))
    (x₀ := x) (s := ball x0 (r / 2)) (bound := fun y => ‖g y‖ * B1) hUx ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hUx] with x' hx'
    refine u2_meas_aux D hg hsupp x' (fun y hy => ?_)
    exact (hDd _ (hfar x' hx' y hy)).continuousAt
  · have hm := u2_meas_aux D hg hsupp x
      (fun y hy => (hDd _ (hfar x hx y hy)).continuousAt)
    refine (hgi.norm.mul_const B0).mono' hm (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul]
    by_cases hy : ‖y‖ ≤ r
    · exact mul_le_mul_of_nonneg_left (hB0 _ (hfar x hx y hy)) (norm_nonneg _)
    · have : g y = 0 := hsupp y (by simpa using hy)
      simp [this]
  · exact u2_meas_aux (fderiv ℝ D) hg hsupp x (fun y hy => hD'c _ (hfar x hx y hy))
  · refine Filter.Eventually.of_forall fun y x' hx' => ?_
    rw [norm_smul]
    by_cases hy : ‖y‖ ≤ r
    · exact mul_le_mul_of_nonneg_left (hB1 _ (hfar x' hx' y hy)) (norm_nonneg _)
    · have : g y = 0 := hsupp y (by simpa using hy)
      simp [this]
  · exact hgi.norm.mul_const B1
  · refine Filter.Eventually.of_forall fun y x' hx' => ?_
    by_cases hy : ‖y‖ ≤ r
    · have hd := (hDd _ (hfar x' hx' y hy)).hasFDerivAt
      have h2 : HasFDerivAt (fun x'' : Euc d => x'' - y) (ContinuousLinearMap.id ℝ (Euc d)) x' :=
        (hasFDerivAt_id x').sub_const y
      have := HasFDerivAt.comp x' hd h2
      rw [ContinuousLinearMap.comp_id] at this
      exact this.const_smul (g y)
    · have : g y = 0 := hsupp y (by simpa using hy)
      simp only [this, zero_smul]
      exact hasFDerivAt_const _ _

end HRS.Whole
