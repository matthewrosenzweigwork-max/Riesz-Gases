import HRS.MS.Fp81S21WickApprox17

/-! Exact finite-coordinate and chart-test identities. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- A finite sum in the coefficient basis reads off its prescribed values. -/
theorem fp81s21_finite_basis_coordinate (m : ℕ) (c : Fin m → ℝ) (j : Fin m) :
    (∑ i : Fin m, c i • fp81s21_coeffBasis i : r26t6_Coeff) j = c j := by
  rw [← fp81s21_coeffBasis_inner_apply]
  simp only [inner_sum, inner_smul_right,
    orthonormal_iff_ite.1 fp81s21_coeffBasis.orthonormal, mul_ite, mul_one, mul_zero]
  simp only [Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Coordinate projections retain exactly the first `m` coordinates. -/
theorem fp81s21_projectField_coordinate (m j : ℕ) (z : r26t6_Coeff) :
    fp81s21_projectField m z j = if j < m then z j else 0 := by
  rw [← fp81s21_coeffBasis_inner_apply, fp81s21_projectField_apply_coordinate]
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.1
    fp81s21_coeffBasis.orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]

/-- A difference between a finite coordinate sum and a projected vector is
supported on the first `m` coordinates. -/
theorem fp81s21_finite_basis_sub_project_supported
    (m : ℕ) (c : Fin m → ℝ) (z : r26t6_Coeff) :
    fp81s21_projectField m
      ((∑ i : Fin m, c i • fp81s21_coeffBasis i) - fp81s21_projectField m z) =
      (∑ i : Fin m, c i • fp81s21_coeffBasis i) - fp81s21_projectField m z := by
  ext j
  rw [fp81s21_projectField_coordinate]
  by_cases hj : j < m
  · simp [hj]
  · simp only [hj, ↓reduceIte, lp.coeFn_sub, Pi.sub_apply, fp81s21_projectField_coordinate, sub_zero]
    rw [← fp81s21_coeffBasis_inner_apply]
    simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.1
      fp81s21_coeffBasis.orthonormal, mul_ite, mul_one, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hne : j ≠ (i : ℕ) := by intro h; subst j; exact hj i.isLt
    simp [hne]

/-- Chart action on the `j`th chart test is exactly coordinate `j`. -/
theorem fp81s21_chartAction_test_coordinate
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (j : ℕ) : fp81s21_chartAction E z (E.test j) = z j := by
  have hcoord : E.encode (E.test j) = (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, hcoord]
  simp [lp.inner_single_right]

#print axioms fp81s21_finite_basis_coordinate
#print axioms fp81s21_projectField_coordinate
#print axioms fp81s21_finite_basis_sub_project_supported
#print axioms fp81s21_chartAction_test_coordinate
end HRS.Fp81.S21
end
