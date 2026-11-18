import HRS.MS.Fp81S21EmbedField11

/-! Export the compact field embedding and its finite coordinate projections. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open scoped RealInnerProductSpace

/-- The coefficient Hilbert basis reads the sequence coordinates. -/
theorem fp81s21_coeffBasis_inner_apply
    (z : r26t6_Coeff) (j : ℕ) :
    inner ℝ (fp81s21_coeffBasis j) z = z j := by
  have h := fp81s21_coeffBasis.repr_apply_apply z j
  rw [← h]
  rfl

/-- The projection agrees with the finite coordinate sum from the task. -/
theorem fp81s21_projectField_apply_coordinate
    (m : ℕ) (z : r26t6_Coeff) :
    fp81s21_projectField m z =
      ∑ j ∈ Finset.range m, z j • fp81s21_coeffBasis j := by
  rw [fp81s21_projectField_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fp81s21_coeffBasis_inner_apply]

/-- The field embedding from the weaker weighted chart to the stronger one is
compact on the Hilbert coefficient space. -/
theorem fp81s21_embedField_isCompactOperator
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    IsCompactOperator (fp81s21_embedField hP hPs Es E) := by
  apply fp81s21_adjoint_isCompactOperator
  exact fp81s21_embedField_primal_isCompactOperator hP hPs E Es

#print axioms HRS.Fp81.S21.fp81s21_coeffBasis_inner_apply
#print axioms HRS.Fp81.S21.fp81s21_projectField_apply_coordinate
#print axioms HRS.Fp81.S21.fp81s21_embedField_isCompactOperator

end HRS.Fp81.S21
