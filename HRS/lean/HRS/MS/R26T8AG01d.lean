import HRS.MS.R26T8AG01c
import HRS.MS.R26T8AG01b
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper d): derivatives of the squared norm and of pair cutoffs

For an inner product space `F`, the squared norm has `‖∂ ‖·‖²(z)‖ = 2‖z‖` and `‖∂² ‖·‖²‖ = 2`.
Composed with a continuous linear map `L : E → F`, `‖∂^k (‖L·‖²)(X)‖ ≤ ‖∂^k(‖·‖²)(L X)‖ ‖L‖^k`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem r26t8a_g01d_sq_fderiv (z : F) :
    fderiv ℝ (fun y : F => ‖y‖ ^ 2) z = (2 : ℝ) • innerSL ℝ z := by
  rw [(hasStrictFDerivAt_norm_sq z).hasFDerivAt.fderiv, ← Nat.cast_smul_eq_nsmul ℝ]
  norm_num

theorem r26t8a_g01d_sq_iter1 (z : F) : ‖iteratedFDeriv ℝ 1 (fun y : F => ‖y‖ ^ 2) z‖ = 2 * ‖z‖ := by
  rw [norm_iteratedFDeriv_one, r26t8a_g01d_sq_fderiv, norm_smul, innerSL_apply_norm]
  norm_num

theorem r26t8a_g01d_sq_iter2 (z : F) : ‖iteratedFDeriv ℝ 2 (fun y : F => ‖y‖ ^ 2) z‖ ≤ 2 := by
  have e : ‖iteratedFDeriv ℝ 2 (fun y : F => ‖y‖ ^ 2) z‖ =
      ‖fderiv ℝ (fderiv ℝ (fun y : F => ‖y‖ ^ 2)) z‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ (fun y : F => ‖y‖ ^ 2)) (x := z)]
    rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : F => ‖y‖ ^ 2) (x := z) (n := 1)]
  rw [e]
  have hfd : fderiv ℝ (fun y : F => ‖y‖ ^ 2) = fun y => (2 : ℝ) • innerSL ℝ y := by
    funext y
    exact r26t8a_g01d_sq_fderiv y
  have hfd2 : fderiv ℝ (fderiv ℝ (fun y : F => ‖y‖ ^ 2)) z = (2 : ℝ) • innerSL ℝ := by
    rw [hfd]
    exact ContinuousLinearMap.fderiv ((2 : ℝ) • innerSL ℝ)
  rw [hfd2]
  refine (r26t8a_g01b_smul_norm (2 : ℝ) (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)).trans ?_
  have hI : ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul, innerSL_apply_norm]
  calc |(2:ℝ)| * ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 2 * 1 := by
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hI (by norm_num)
    _ = 2 := by norm_num

end HRS.MS.R26T8A

end
