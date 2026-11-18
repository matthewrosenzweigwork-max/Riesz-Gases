import HRS.MS.Fp81S21EmbedField13

/-! The weighted chart field embedding is contractive on the coefficient Hilbert space. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111
open scoped RealInnerProductSpace

/-- The field embedding is a contraction, since it is the adjoint of the
contractive primal chart inclusion. -/
theorem fp81s21_embedField_norm_le_one
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    ‖fp81s21_embedField hP hPs Es E‖ ≤ 1 := by
  calc
    ‖fp81s21_embedField hP hPs Es E‖ =
        ‖(fp81s21_embedField_primal hP hPs E Es).adjoint‖ := rfl
    _ = ‖fp81s21_embedField_primal hP hPs E Es‖ :=
      fp81s21_adjoint_opNorm_eq (fp81s21_embedField_primal hP hPs E Es)
    _ ≤ 1 := fp81s21_embedField_primal_norm_le hP hPs E Es

#print axioms HRS.Fp81.S21.fp81s21_embedField_norm_le_one

end HRS.Fp81.S21
