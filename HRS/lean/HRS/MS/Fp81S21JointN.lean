import HRS.MS.Fp81S21JointC
import HRS.MS.Fp81S21JointG7

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

/-- The Gaussian and particle joint constructions use the same projection
onto the quadratic coordinate. -/
theorem fp81s21_jointN_partialCenter_eq (H : ℝ) :
    fp81s21_jointG_partialCenter H = fp81s21_jointC_partialCenter H := by
  rfl

#print axioms fp81s21_jointN_partialCenter_eq

end HRS.Fp81.S21

end
