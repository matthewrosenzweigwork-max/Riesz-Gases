import HRS.MS.Fp81S21EmbedField7

/-! The dual field embedding is the Hilbert adjoint of the compact primal
inclusion. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open scoped RealInnerProductSpace

/-- The field embedding associated to the primal weighted inclusion. -/
def fp81s21_embedField
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    r26t6_Coeff →L[ℝ] r26t6_Coeff :=
  (fp81s21_embedField_primal hP hPs E Es).adjoint

/-- The dual field embedding transports the chart action exactly on tests. -/
theorem fp81s21_embedField_action
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (z : r26t6_Coeff) (f : Euc d → ℝ) (hf : IsR2Test f) :
    fp81s21_chartAction E (fp81s21_embedField hP hPs Es E z) f =
      fp81s21_chartAction Es z f := by
  change inner ℝ ((fp81s21_embedField_primal hP hPs E Es).adjoint z)
      (E.encode f) = inner ℝ z (Es.encode f)
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [fp81s21_embedField_primal_apply_test hP hPs E Es f hf]

#print axioms HRS.Fp81.S21.fp81s21_embedField_action

end HRS.Fp81.S21
