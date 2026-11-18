import HRS.MS.CritForceMom8

/-!
# S8.2 NormalForm packet R03, part 9: logarithm bounds
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

lemma s82n_log_le_two_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h1 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← Real.sq_sqrt hy.le]
    rw [pow_two, Real.log_mul hs.ne' hs.ne']; ring
  have h2 := Real.log_le_sub_one_of_pos hs
  linarith

lemma s82n_log_sq_le_inv (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : (Real.log r) ^ 2 ≤ 4 / r := by
  have h := s82n_log_le_two_sqrt (1 / r) (by positivity)
  have hl : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  rw [hl] at h
  have h0 : 0 ≤ -Real.log r := by
    have := Real.log_nonpos hr.le hr1; linarith
  have h2 : (-Real.log r) ^ 2 ≤ (2 * Real.sqrt (1 / r)) ^ 2 := pow_le_pow_left₀ h0 h 2
  have h3 : (2 * Real.sqrt (1 / r)) ^ 2 = 4 / r := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  nlinarith

/-- `log² r ≤ 2 ℓ² + 2 Λ² + (8/s²) A / r^s` for `0 < r ≤ r0`, `ℓ = log A / s`, `Λ = log r0 - ℓ`. -/
lemma s82n_log_sq_le (s r0 A r : ℝ) (hs : 0 < s) (hA : 0 < A) (hr : 0 < r) (hrr : r ≤ r0) :
    (Real.log r) ^ 2 ≤ 2 * (Real.log A / s) ^ 2 + 2 * (Real.log r0 - Real.log A / s) ^ 2 +
      (8 / s ^ 2) * (A / r ^ s) := by
  have hr0 : 0 < r0 := lt_of_lt_of_le hr hrr
  set ℓ := Real.log A / s with hℓ
  set δ := Real.log r - ℓ with hδ
  have hsplit : (Real.log r) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * δ ^ 2 := by
    have : Real.log r = ℓ + δ := by rw [hδ]; ring
    rw [this]; nlinarith [sq_nonneg (ℓ - δ)]
  have hδb : δ ^ 2 ≤ (Real.log r0 - ℓ) ^ 2 + (4 / s ^ 2) * (A / r ^ s) := by
    have hy : 0 < A / r ^ s := by have := Real.rpow_pos_of_pos hr s; positivity
    rcases le_or_gt 0 δ with h | h
    · have h1 : δ ≤ Real.log r0 - ℓ := by
        have := Real.log_le_log hr hrr; rw [hδ]; linarith
      have : δ ^ 2 ≤ (Real.log r0 - ℓ) ^ 2 := pow_le_pow_left₀ h h1 2
      have : 0 ≤ (4 / s ^ 2) * (A / r ^ s) := by positivity
      linarith
    · have h1 : -δ = Real.log (A / r ^ s) / s := by
        rw [Real.log_div hA.ne' (Real.rpow_pos_of_pos hr s).ne', Real.log_rpow hr, hδ, hℓ]
        field_simp; ring
      have h2 := s82n_log_le_two_sqrt (A / r ^ s) hy
      have h3 : -δ ≤ 2 * Real.sqrt (A / r ^ s) / s := by
        rw [h1]; exact div_le_div_of_nonneg_right h2 hs.le
      have h4 : (-δ) ^ 2 ≤ (2 * Real.sqrt (A / r ^ s) / s) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
      have h5 : (2 * Real.sqrt (A / r ^ s) / s) ^ 2 = (4 / s ^ 2) * (A / r ^ s) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hy.le]; ring
      have : 0 ≤ (Real.log r0 - ℓ) ^ 2 := sq_nonneg _
      nlinarith
  have e : 8 / s ^ 2 * (A / r ^ s) = 2 * (4 / s ^ 2 * (A / r ^ s)) := by ring
  linarith

end HRS.MS.S82N
