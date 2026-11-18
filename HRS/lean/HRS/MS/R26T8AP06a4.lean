import HRS.MS.R26T8AP06a3
import HRS.MS.R26T8AP00

/-!
# S8.2 P06a (4): the limit jets `T_j` of a source with negative conormal order
For `j < min(-sigma, k)` the jet `D^j h` of a function with `‖D^j h(z)‖ <= A (1 + |z|^(-(sigma+j)) (1+|log|z||)^b)` has a limit
`T_j` at `0` (dimension `>= 2`), symmetric, with `‖D^j h(z) - T_j‖ <= C A |z|^a (1+|log|z||)^b`, `a = min(-(sigma+j), 1)`.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

/-- Bound for `s^c (1+|log s|)^b` on `(0,1]`. -/
def r26t8a_p06_M (c : ℝ) (b : ℕ) : ℝ := (b.factorial : ℝ) * (c⁻¹) ^ b * Real.exp c

theorem r26t8a_p06_slog (b : ℕ) {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ c * (1 + |Real.log s|) ^ b ≤ r26t8a_p06_M c b := by
  set t := -Real.log s with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [Real.log_nonpos hs.le hs1]
  have habs : |Real.log s| = t := by rw [abs_of_nonpos (Real.log_nonpos hs.le hs1)]
  have hsc : s ^ c = Real.exp (-(c * t)) := by
    rw [Real.rpow_def_of_pos hs]; congr 1; rw [ht]; ring
  have h1 := Real.pow_div_factorial_le_exp (x := c * (1 + t)) (by positivity) b
  have hf : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have h2 : (c * (1 + t)) ^ b ≤ (b.factorial : ℝ) * Real.exp (c * (1 + t)) := by
    rw [div_le_iff₀ hf] at h1; linarith
  have h3 : (1 + t) ^ b = (c * (1 + t)) ^ b * (c⁻¹) ^ b := by
    rw [← mul_pow, show c * (1 + t) * c⁻¹ = 1 + t by field_simp]
  rw [habs, hsc, h3, r26t8a_p06_M]
  have h4 : Real.exp (-(c * t)) * Real.exp (c * (1 + t)) = Real.exp c := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-(c * t)) * ((c * (1 + t)) ^ b * (c⁻¹) ^ b)
      ≤ Real.exp (-(c * t)) * ((b.factorial : ℝ) * Real.exp (c * (1 + t)) * (c⁻¹) ^ b) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
    _ = (b.factorial : ℝ) * (c⁻¹) ^ b * (Real.exp (-(c * t)) * Real.exp (c * (1 + t))) := by ring
    _ = _ := by rw [h4]

end HRS.MS.R26T8A
