import HRS.MS.R26T8AZ5c
import HRS.MS.R26T8AP16a

/-!
# S8.2 T8A Z5a1: `r^a (1+|log r|)^b` is bounded on `(0,1]` for every `a > 0`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_Z5a1_log_bound {a : ℝ} (ha : 0 < a) (b : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → r ^ a * (1 + |Real.log r|) ^ b ≤ c := by
  refine ⟨(1 + ((b : ℝ) + 1) / a) ^ b, by positivity, fun r hr0 hr1 => ?_⟩
  set y : ℝ := 1 / r with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hr0]; linarith
  have hy0 : 0 < y := by linarith
  have hlog : |Real.log r| = Real.log y := by
    rw [hy, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  set ε : ℝ := a / ((b : ℝ) + 1) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have h1 := Real.log_le_rpow_div hy0.le hε0
  have hyε : 1 ≤ y ^ ε := Real.one_le_rpow hy1 hε0.le
  have hc1 : (0 : ℝ) ≤ 1 / ε := by positivity
  have h2 : 1 + Real.log y ≤ (1 + ((b : ℝ) + 1) / a) * y ^ ε := by
    have e : y ^ ε / ε = (((b : ℝ) + 1) / a) * y ^ ε := by rw [hε]; field_simp
    nlinarith [div_nonneg (Nat.cast_add_one_pos b).le ha.le]
  have h3 : (1 + Real.log y) ^ b ≤ ((1 + ((b : ℝ) + 1) / a) * y ^ ε) ^ b :=
    pow_le_pow_left₀ (by have := Real.log_nonneg hy1; linarith) h2 b
  have hp : (y ^ ε) ^ b = y ^ (ε * (b : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
  have h5 : r ^ a * y ^ (ε * (b : ℝ)) ≤ 1 := by
    have : y ^ (ε * (b : ℝ)) = r ^ (-(ε * (b : ℝ))) := by
      rw [hy, one_div, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
    rw [this, ← Real.rpow_add hr0]
    refine Real.rpow_le_one hr0.le hr1 ?_
    have : a + -(ε * (b : ℝ)) = a / ((b : ℝ) + 1) := by rw [hε]; field_simp; ring
    rw [this]; positivity
  rw [hlog]
  calc r ^ a * (1 + Real.log y) ^ b ≤ r ^ a * ((1 + ((b : ℝ) + 1) / a) ^ b * (y ^ ε) ^ b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← mul_pow]; exact h3
    _ = (1 + ((b : ℝ) + 1) / a) ^ b * (r ^ a * y ^ (ε * (b : ℝ))) := by rw [hp]; ring
    _ ≤ (1 + ((b : ℝ) + 1) / a) ^ b * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := mul_one _

end HRS.MS.R26T8A
