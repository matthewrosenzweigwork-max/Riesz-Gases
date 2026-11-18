import HRS.MS.ProClosureS111WeightedCutoff

/-! Pointwise estimates for the source-jet envelope. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.ProClosureS111 HRS.MS.FixEq

/-- Removing the weight from the ordered-jet estimate costs one factor of
`jbracket x ^ P`. No boundedness of the input jets is assumed. -/
theorem fp81s21_weighted_iterated_le_unweighted {d r : ℕ} {P : ℝ}
    (f : Euc d → ℝ) {j : ℕ} (hj : j ≤ r) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤
      ((d : ℝ) + 1) ^ r * (jbracket x ^ P) * ‖weightedJets r P f x‖ := by
  have hp : 0 < jbracket x ^ P := Real.rpow_pos_of_pos (s57p_jbracket_pos x) _
  have h := weighted_iterated_le_jets (Pw := P) f hj x
  have he : jbracket x ^ (-P) = (jbracket x ^ P)⁻¹ := by
    rw [Real.rpow_neg (s57p_jbracket_pos x).le]
  rw [he] at h
  have h' := mul_le_mul_of_nonneg_left h hp.le
  calc
    _ = (jbracket x ^ P) * ((jbracket x ^ P)⁻¹ * ‖iteratedFDeriv ℝ j f x‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ ≤ (jbracket x ^ P) * (((d : ℝ) + 1) ^ r * ‖weightedJets r P f x‖) := h'
    _ = _ := by ring

#print axioms HRS.Fp81.S21.fp81s21_weighted_iterated_le_unweighted
end HRS.Fp81.S21
