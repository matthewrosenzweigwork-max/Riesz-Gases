import HRS.MS.Fp81S21WickApprox
import HRS.MS.Fp81S21EmbedField12

/-! Mean-square errors of finitely many coefficient coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS.MS.R26T6

/-- Parseval combines `m` scalar squared-error bounds into a coefficient-field
squared-error bound, including integrability. -/
theorem fp81s21_finite_coordinate_sqerr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x y : Ω → r26t6_Coeff) (m : ℕ) (ε : ℝ)
    (hsupport : ∀ᵐ ω ∂P, fp81s21_projectField m (x ω - y ω) = x ω - y ω)
    (hcoord : ∀ j ∈ Finset.range m,
      fp81s21_SqErr P (fun ω => x ω j) (fun ω => y ω j) ε) :
    fp81s21_SqErr P x y (Real.sqrt (m : ℝ) * ε) := by
  have he : ∀ i j : ℕ, inner ℝ (fp81s21_coeffBasis i) (fp81s21_coeffBasis j) =
      if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 fp81s21_coeffBasis.orthonormal
  have hsq : ∀ z : r26t6_Coeff, ‖fp81s21_projectField m z‖ ^ 2 =
      ∑ j ∈ Finset.range m, (z j) ^ 2 := by
    intro z
    rw [← real_inner_self_eq_norm_sq, fp81s21_projectField_apply]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, he, conj_trivial]
    simp only [Finset.sum_ite_eq', sq]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj, fp81s21_coeffBasis_inner_apply, pow_two]
  have heq : (fun ω => ‖x ω - y ω‖ ^ 2) =ᵐ[P]
      (fun ω => ∑ j ∈ Finset.range m, ‖x ω j - y ω j‖ ^ 2) := by
    filter_upwards [hsupport] with ω hω
    rw [← hω, hsq]
    simp [Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ω => ∑ j ∈ Finset.range m,
      ‖x ω j - y ω j‖ ^ 2) P :=
    integrable_finset_sum _ (fun j hj => (hcoord j hj).1)
  refine ⟨hint.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finset_sum _ (fun j hj => (hcoord j hj).1)]
  calc
    _ ≤ ∑ _j ∈ Finset.range m, ε ^ 2 :=
      Finset.sum_le_sum (fun j hj => (hcoord j hj).2)
    _ = (Real.sqrt (m : ℝ) * ε) ^ 2 := by
      simp [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

#print axioms fp81s21_finite_coordinate_sqerr
end HRS.Fp81.S21
end
