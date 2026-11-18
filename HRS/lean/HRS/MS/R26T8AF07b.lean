import HRS.MS.R26T8AF07a

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07b): generator = local part + nonlocal part

`generatorW (critCoeff) 0 f x = r26t8a_localP f x + oneJ (critCoeff) f x` and the iterate recursion
`r26t8a_LIter (j+1) f = generatorW 0 (r26t8a_LIter j f)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07b_nu (a beta : ℝ) (rho : Euc d → ℝ) :
    (critCoeff d a beta rho).ν = beta⁻¹ := by
  simp [critCoeff, quadraticGradientDyn, WholeDyn.coeff]

theorem r26t8a_f07b_localP_split (a beta : ℝ) (rho f : Euc d → ℝ) (x : Euc d) :
    r26t8a_localP a beta rho f x =
      (critCoeff d a beta rho).ν * Laplacian.laplacian f x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (gradient f x) := by
  rw [r26t8a_f07b_nu, r26t8a_f07a_drift, inner_sub_left, inner_neg_left,
    real_inner_smul_left, r26t8a_f07a_inner_grad]
  unfold r26t8a_localP forceMean
  ring

theorem r26t8a_f07b_generator_split (a beta : ℝ) (rho f : Euc d → ℝ) (x : Euc d) :
    generatorW (critCoeff d a beta rho) 0 f x =
      r26t8a_localP a beta rho f x + oneJ (critCoeff d a beta rho) f x := by
  rw [r26t8a_f07b_localP_split]
  unfold oneJ
  ring

theorem r26t8a_f07b_LIter_succ (a beta : ℝ) (rho : Euc d → ℝ) (j : ℕ) (f : Euc d → ℝ) :
    r26t8a_LIter a beta rho (j + 1) f =
      generatorW (critCoeff d a beta rho) 0 (r26t8a_LIter a beta rho j f) := by
  unfold r26t8a_LIter
  rw [Function.iterate_succ_apply']

end HRS.MS.R26T8A

end
