import HRS.MS.MfeConfAux124

/-!
# S.B.1 (SB5), R1 (part 2): the force defect as a difference of cancellation-convention convolutions

* `sb1_cv_eq_rgT`: for an odd bounded kernel `f`, `∫ φ(y) f(x-y) dy = rgT f φ x` (the cancellation term vanishes by oddness).
* `sb1_e_eq_rgT`: `e_j = ∂_j(k*ρ) - F_j = rgT (∂_jk) ρ - rgT (∂_jg) ρ` for the regularising kernel `k`.
* for `k = k_M = sb1kM`: `∂_jk_M` is an `RgKer` with a constant uniform in `M`, and agrees with `∂_jg` outside the ball of radius `r_M`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_cv_eq_rgT {f φ : Euc d → ℝ} (hfm : Measurable f) {L : ℝ} (hL : ∀ z, |f z| ≤ L)
    (hodd : ∀ z, f (-z) = -f z) (hφ : Integrable φ) (x : Euc d) :
    sb1_lv_cv f φ x = rgT f φ x := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hi1 : Integrable (fun z : Euc d => f z * φ (x - z)) := by
    refine ((hφ.comp_sub_left x).norm.const_mul L).mono' (hfm.aestronglyMeasurable.mul
      (hφ.comp_sub_left x).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hL z) (norm_nonneg _)
  set S : Set (Euc d) := Metric.closedBall 0 (1 / 4) with hS
  have hSm : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hfS : IntegrableOn f S := by
    refine Measure.integrableOn_of_bounded (M := L) (measure_closedBall_lt_top).ne hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hL z
  have hI0 : ∫ z in S, f z = 0 := by
    have h1 : ∫ z, Set.indicator S f z = ∫ z, Set.indicator S f (-z) := (integral_neg_eq_self (Set.indicator S f) volume).symm
    have h2 : ∀ z, Set.indicator S f (-z) = -Set.indicator S f z := by
      intro z
      by_cases hz : z ∈ S
      · have : -z ∈ S := by simpa [hS] using hz
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem this, hodd]
      · have : -z ∉ S := by simpa [hS] using hz
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem this, neg_zero]
    simp only [h2, integral_neg] at h1
    rw [← integral_indicator hSm]
    linarith
  have hrw : ∀ z, f z • rgR φ x z = f z * φ (x - z) - Set.indicator S (fun z => f z * φ x) z := by
    intro z
    unfold rgR
    by_cases hz : ‖z‖ ≤ 1 / 4
    · have hzS : z ∈ S := by simpa [hS] using hz
      simp only [hz, if_true]; rw [Set.indicator_of_mem hzS, smul_eq_mul]; ring
    · have hzS : z ∉ S := by simpa [hS] using hz
      simp only [hz, if_false]; rw [Set.indicator_of_notMem hzS, smul_eq_mul]; ring
  unfold sb1_lv_cv rgT
  simp only [hrw]
  have hi2 : Integrable (Set.indicator S (fun z => f z * φ x)) := by
    rw [integrable_indicator_iff hSm]
    exact (hfS.mul_const (φ x))
  rw [integral_sub hi1 hi2, integral_indicator hSm, integral_mul_const, hI0, zero_mul, sub_zero]
  have := integral_sub_left_eq_self (fun y : Euc d => φ y * f (x - y)) volume x
  simp only [sub_sub_cancel] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

end HRS.MS.MfeConf
