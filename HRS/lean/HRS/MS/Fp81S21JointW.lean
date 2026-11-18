import HRS.MS.Fp81S21RankKernel
import HRS.MS.Fp81S21QuadPoly

/-! Finite-rank Gaussian quadratic polynomials and their centering. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The raw finite-rank quadratic polynomial at a single oscillator dual. -/
def fp81s21_polyAt {d : ℕ} (D : fp81s21_RankKernel d)
    (x : OscDual d (wholeSpaceIndex d : ℝ)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j * OscDual.eval x (D.u i) * OscDual.eval x (D.u j)

/-- Single-time and path formulations use the same raw polynomial. -/
theorem fp81s21_polyAt_path {d : ℕ} (D : fp81s21_RankKernel d) {H : ℝ}
    (x : OscPath d (wholeSpaceIndex d : ℝ) H) (t : Set.Icc (0 : ℝ) H) :
    fp81s21_polyAt D (OscPath.at' x t) = fp81s21_quadPoly D.c D.u x t := rfl

/-- Centering a finite quadratic polynomial equals the usual Wick subtraction. -/
theorem fp81s21_center_finite_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (c : Fin n → Fin n → ℝ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (ω : Ω) :
    fp81s21_center P (fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j,
      c i j * X i ω * X j ω) ω =
      (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
        (X i ω * X j ω - ∫ ω', X i ω' * X j ω' ∂P) := by
  have hp : ∀ i j, Integrable (fun ω => c i j * X i ω * X j ω) P := by
    intro i j
    convert ((hX i).integrable_mul (hX j)).const_mul (c i j) using 1 <;> ext ω <;> simp only [Pi.mul_apply] <;> ring
  have hs : ∀ i, Integrable (fun ω => ∑ j, c i j * X i ω * X j ω) P := by
    intro i
    exact integrable_finset_sum _ (fun j _ => hp i j)
  unfold fp81s21_center
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hs i)]
  simp_rw [integral_finset_sum _ (fun j _ => hp _ j)]
  simp_rw [show ∀ i j, (∫ ω', c i j * X i ω' * X j ω' ∂P) =
      c i j * ∫ ω', X i ω' * X j ω' ∂P by
    intro i j
    simp_rw [show ∀ ω', c i j * X i ω' * X j ω' =
      c i j * (X i ω' * X j ω') by intro ω'; ring]
    rw [integral_const_mul]]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

#print axioms fp81s21_polyAt_path
#print axioms fp81s21_center_finite_polynomial
end HRS.Fp81.S21
end
