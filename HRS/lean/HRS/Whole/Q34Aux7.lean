import HRS.Whole.Q34Aux4

/-!
# Packet Q34, helper file 7: Cauchy-Schwarz and Young's `L¹ * L²` inequality (lintegral form)
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

/-- Cauchy-Schwarz for a nonnegative function against an arbitrary measure. -/
theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (m : Measure α) (F : α → ℝ≥0∞)
    (hF : AEMeasurable F m) :
    (∫⁻ a, F a ∂m) ^ 2 ≤ m univ * ∫⁻ a, F a ^ 2 ∂m := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m (p := 2) (q := 2)
    (by exact Real.HolderConjugate.two_two) hF (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const] at h
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 := pow_le_pow_left' h 2
  rw [mul_pow, hsq, hsq] at h2
  simpa [ENNReal.rpow_two, mul_comm] using h2


theorem weighted_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (G F : α → ℝ≥0∞)
    (hG : Measurable G) (hF : Measurable F) :
    (∫⁻ a, G a * F a ∂μ) ^ 2 ≤ (∫⁻ a, G a ∂μ) * ∫⁻ a, G a * F a ^ 2 ∂μ := by
  have h := sq_lintegral_le (μ.withDensity G) F hF.aemeasurable
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ hG hF,
    lintegral_withDensity_eq_lintegral_mul _ hG (hF.pow_const 2)] at h
  simpa using h

/-- Young's inequality `‖G * F‖₂ ≤ ‖G‖₁ ‖F‖₂` in `lintegral` form. -/
theorem young_L1_L2 (G F : Euc d → ℝ≥0∞) (hG : Measurable G) (hF : Measurable F) :
    ∫⁻ x, (∫⁻ w, G w * F (x - w)) ^ 2 ≤ (∫⁻ w, G w) ^ 2 * ∫⁻ x, F x ^ 2 := by
  have hFx : ∀ x : Euc d, Measurable (fun w : Euc d => F (x - w)) := fun x =>
    hF.comp (measurable_const.sub measurable_id)
  have h1 : ∀ x : Euc d, (∫⁻ w, G w * F (x - w)) ^ 2 ≤
      (∫⁻ w, G w) * ∫⁻ w, G w * F (x - w) ^ 2 := fun x =>
    weighted_cs volume G (fun w => F (x - w)) hG (hFx x)
  calc ∫⁻ x, (∫⁻ w, G w * F (x - w)) ^ 2
      ≤ ∫⁻ x, (∫⁻ w, G w) * ∫⁻ w, G w * F (x - w) ^ 2 := lintegral_mono h1
    _ = (∫⁻ w, G w) * ∫⁻ x, ∫⁻ w, G w * F (x - w) ^ 2 := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right'
          (f := fun p : Euc d × Euc d => G p.2 * F (p.1 - p.2) ^ 2)
          ((hG.comp measurable_snd).mul ((hF.comp (measurable_fst.sub measurable_snd)).pow_const 2))
    _ = (∫⁻ w, G w) * ∫⁻ w, ∫⁻ x, G w * F (x - w) ^ 2 := by
        congr 1
        exact lintegral_lintegral_swap
          (((hG.comp measurable_snd).mul
            ((hF.comp (measurable_fst.sub measurable_snd)).pow_const 2)).aemeasurable)
    _ = (∫⁻ w, G w) * ∫⁻ w, G w * ∫⁻ x, F x ^ 2 := by
        congr 1
        refine lintegral_congr fun w => ?_
        have hm : Measurable (fun x : Euc d => F (x - w) ^ 2) := by fun_prop
        rw [lintegral_const_mul _ hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => F x ^ 2) w
    _ = (∫⁻ w, G w) ^ 2 * ∫⁻ x, F x ^ 2 := by
        rw [lintegral_mul_const _ hG]
        ring

end HRS.Whole.Q34
