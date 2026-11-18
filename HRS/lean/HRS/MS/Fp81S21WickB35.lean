import HRS.MS.Fp81S21WickB34

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The block construction represents the difference of the two kernels. -/
theorem fp81s21_wickB35_kernel_concat
    {d m n : ℕ} (u : Fin m → Euc d → ℝ) (v : Fin n → Euc d → ℝ)
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ) :
    fp81s21_wickG_finite_rank_kernel (fp81s21_wickB22_concatFunction u v)
        (fp81s21_wickB22_concatCoeff c c') =
      fun z => fp81s21_wickG_finite_rank_kernel u c z -
        fp81s21_wickG_finite_rank_kernel v c' z := by
  classical
  funext z
  change r2FiniteRankKernel (fp81s21_wickB22_concatCoeff c c')
      (fp81s21_wickB22_concatFunction u v) z.1 z.2 = _
  simp [r2FiniteRankKernel, fp81s21_wickG_finite_rank_kernel,
    fp81s21_wickB22_concatCoeff, fp81s21_wickB22_concatFunction,
    fp81s21_wickB22_splitIndex, Fin.sum_univ_add]
  ring

/-- Scaling the coefficient matrix scales its kernel. -/
theorem fp81s21_wickB35_kernel_smul
    {d m : ℕ} (u : Fin m → Euc d → ℝ) (c : Fin m → Fin m → ℝ) (a : ℝ) :
    fp81s21_wickG_finite_rank_kernel u (fun i j => a * c i j) =
      fun z => a * fp81s21_wickG_finite_rank_kernel u c z := by
  classical
  funext z
  simp only [fp81s21_wickG_finite_rank_kernel, r2FiniteRankKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms fp81s21_wickB35_kernel_concat
#print axioms fp81s21_wickB35_kernel_smul

end HRS.Fp81.S21
end
