import HRS.MS.Fp81S21WickG14

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The finite half-Wick polynomial is pointwise linear in its coefficient
matrix. -/
theorem fp81s21_wickB2_polynomial_add_coeff
    {d m : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c c' : Fin m → Fin m → ℝ) :
    fp81s21_wickG_finite_rank_polynomial L u hu (fun i j => c i j + c' i j) =
      fun ω => fp81s21_wickG_finite_rank_polynomial L u hu c ω +
        fp81s21_wickG_finite_rank_polynomial L u hu c' ω := by
  funext ω
  simp only [fp81s21_wickG_finite_rank_polynomial, add_mul,
    Finset.sum_add_distrib]
  ring

/-- The finite half-Wick polynomial is pointwise homogeneous in its
coefficient matrix. -/
theorem fp81s21_wickB2_polynomial_smul_coeff
    {d m : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (a : ℝ) (c : Fin m → Fin m → ℝ) :
    fp81s21_wickG_finite_rank_polynomial L u hu (fun i j => a * c i j) =
      fun ω => a * fp81s21_wickG_finite_rank_polynomial L u hu c ω := by
  funext ω
  change (1 / 2 : ℝ) *
      ∑ i, ∑ j, (a * c i j) *
        ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
          ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P) =
    a * ((1 / 2 : ℝ) *
      ∑ i, ∑ j, c i j *
        ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
          ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P))
  calc
    (1 / 2 : ℝ) * ∑ i, ∑ j, (a * c i j) *
        ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
          ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P) =
      (1 / 2 : ℝ) * ∑ i, a * ∑ j, c i j *
        ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
          ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P) := by
            apply congrArg (fun x : ℝ => (1 / 2 : ℝ) * x)
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ j, (a * c i j) *
                  ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
                    ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P) =
                ∑ j, a * (c i j *
                  ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
                    ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
              _ = a * ∑ j, c i j *
                  ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
                    ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P) := by
                      rw [← Finset.mul_sum]
    _ = (1 / 2 : ℝ) *
        (a * ∑ i, ∑ j, c i j *
          ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
            ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P)) := by
          apply congrArg (fun x : ℝ => (1 / 2 : ℝ) * x)
          rw [← Finset.mul_sum]
    _ = a * ((1 / 2 : ℝ) *
        ∑ i, ∑ j, c i j *
          ((L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
            ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P)) := by
          ring

#print axioms fp81s21_wickB2_polynomial_add_coeff
#print axioms fp81s21_wickB2_polynomial_smul_coeff

end HRS.Fp81.S21

end
