import HRS.MS.R26T8AZ5b

/-!
# S8.2 T8A Y5a: the weak envelope of the order-zero Riesz bound (gain `α`) is dominated by a constant when `q = 0` or `|z| ≥ 1/4`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_Y5a_weak_env (b k : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ Kw : ℝ, 1 ≤ Kw ∧ ∀ (q : ℕ), q ≤ k → ∀ r : ℝ, 0 < r → r ≤ 1 → (q = 0 ∨ 1 / 4 ≤ r) →
      1 + r ^ (-((0 - α : ℝ) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) ≤ Kw := by
  obtain ⟨c, hc0, hc⟩ := r26t8a_Z5a1_log_bound (a := α) hα (b + 1)
  refine ⟨1 + c + 4 ^ (α + (k : ℝ)) * 4 ^ (b + 1), ?_, fun q hq r hr0 hr1 hcase => ?_⟩
  · have : (0 : ℝ) ≤ 4 ^ (α + (k : ℝ)) * 4 ^ (b + 1) := by positivity
    linarith
  rcases hcase with rfl | h4
  · have := hc r hr0 hr1
    have e : r ^ (-((0 - α : ℝ) + ((0 : ℕ) : ℝ))) = r ^ α := by simp
    rw [e]
    have : (0 : ℝ) ≤ 4 ^ (α + (k : ℝ)) * 4 ^ (b + 1) := by positivity
    linarith
  · have h1 := r26t8a_Z5b_rpow_le h4 hr1 (-((0 - α : ℝ) + (q : ℝ)))
    have h2 : |-((0 - α : ℝ) + (q : ℝ))| ≤ α + k := by
      rw [abs_le]
      have : (q : ℝ) ≤ k := by exact_mod_cast hq
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      constructor <;> linarith
    have h3 : (4 : ℝ) ^ |-((0 - α : ℝ) + (q : ℝ))| ≤ 4 ^ (α + (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have hL : (1 + |Real.log r|) ^ (b + 1) ≤ 4 ^ (b + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have hlog : |Real.log r| ≤ Real.log 4 := by
        rw [abs_le]; constructor
        · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) h4
          rw [one_div, Real.log_inv] at this; linarith
        · have := Real.log_le_log hr0 hr1
          rw [Real.log_one] at this
          linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
      have : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
      linarith
    have h5 : r ^ (-((0 - α : ℝ) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) ≤
        4 ^ (α + (k : ℝ)) * 4 ^ (b + 1) :=
      mul_le_mul (h1.trans h3) hL (by positivity) (by positivity)
    linarith

end HRS.MS.R26T8A
