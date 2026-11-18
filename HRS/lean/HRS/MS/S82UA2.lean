import HRS.MS.S82UA1

/-!
# S8.2 A01 (S82U): the grouped-edge estimate
For distinct `u v w`: `|<G(u-v), ∇_1 Q(u,w) - ∇_1 Q(v,w)>| ≤ C A W pole(u,v) (pole(u,w) + pole(v,w))`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

lemma u_min_pos {a : ℝ} (ha : 0 < a) : 0 < min 1 a := lt_min one_pos ha

lemma u_rpow_neg_le_min {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) :
    a ^ (-s) ≤ (min 1 a) ^ (-s) :=
  Real.rpow_le_rpow_of_nonpos (u_min_pos ha) (min_le_right _ _) (by linarith)

lemma u_scalar {s a b κ : ℝ} (hs : 1 ≤ s) (ha : 0 < a) (hb : 0 < b) (hκ : 1 ≤ κ)
    (hba : b ≤ κ * a) :
    a ^ (-s - 1) * (1 + (min 1 b) ^ (1 - s)) ≤
      2 * κ * ((1 + (min 1 a) ^ (-s)) * (1 + (min 1 b) ^ (-s))) := by
  have hra := u_min_pos ha
  have hrb := u_min_pos hb
  have e1 : a ^ (-s - 1) = a ^ (-s) * a⁻¹ := by
    rw [Real.rpow_sub ha, Real.rpow_one, div_eq_mul_inv]
  have e2 : a ^ (-s) ≤ (min 1 a) ^ (-s) := u_rpow_neg_le_min (by linarith) ha
  have hclaim : a⁻¹ * (1 + (min 1 b) ^ (1 - s)) ≤ 2 * κ * (1 + (min 1 b) ^ (-s)) := by
    have hrbpow : 0 ≤ (min 1 b) ^ (-s) := Real.rpow_nonneg hrb.le _
    by_cases hb1 : b ≤ 1
    · rw [min_eq_right hb1]
      have h1 : a⁻¹ ≤ κ * b⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one, div_le_div_iff₀ ha hb]
        nlinarith
      have h2 : b ^ (1 - s) = b * b ^ (-s) := by
        rw [show 1 - s = 1 + -s by ring, Real.rpow_add hb, Real.rpow_one]
      have h3 : b⁻¹ ≤ b ^ (-s) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)
      have h4 : 0 ≤ b ^ (-s) := Real.rpow_nonneg hb.le _
      have hbb : b⁻¹ * b = 1 := inv_mul_cancel₀ hb.ne'
      calc a⁻¹ * (1 + b ^ (1 - s)) ≤ κ * b⁻¹ * (1 + b ^ (1 - s)) :=
            mul_le_mul_of_nonneg_right h1 (by rw [h2]; positivity)
        _ = κ * (b⁻¹ + b ^ (-s)) := by rw [h2]; field_simp
        _ ≤ κ * (b ^ (-s) + b ^ (-s)) := by gcongr
        _ ≤ 2 * κ * (1 + b ^ (-s)) := by nlinarith
    · push_neg at hb1
      rw [min_eq_left hb1.le, Real.one_rpow, Real.one_rpow]
      have h1 : a⁻¹ ≤ κ := by
        rw [inv_eq_one_div, div_le_iff₀ ha]
        nlinarith
      nlinarith
  calc a ^ (-s - 1) * (1 + (min 1 b) ^ (1 - s)) = a ^ (-s) * (a⁻¹ * (1 + (min 1 b) ^ (1 - s))) := by
        rw [e1]; ring
    _ ≤ (min 1 a) ^ (-s) * (2 * κ * (1 + (min 1 b) ^ (-s))) := by
        apply mul_le_mul e2 hclaim (by positivity) (Real.rpow_nonneg hra.le _)
    _ ≤ 2 * κ * ((1 + (min 1 a) ^ (-s)) * (1 + (min 1 b) ^ (-s))) := by
        have : 0 ≤ (min 1 b) ^ (-s) := Real.rpow_nonneg hrb.le _
        have : 0 ≤ (min 1 a) ^ (-s) := Real.rpow_nonneg hra.le _
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * κ) (by positivity : (0:ℝ) ≤ (1 + (min 1 b) ^ (-s)))]

end HRS.MS.S82U
