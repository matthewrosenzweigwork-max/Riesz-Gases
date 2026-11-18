import HRS.MS.R26T8AF05b

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07a): the generator splits as local part plus nonlocal part

For the critical coefficients, `generatorW C 0 f = localP f + oneJ C f` pointwise (`localP` of F00 is the
local part `β⁻¹Δf - a x·∇f - F·∇f` with the thermal force `F = forceMean ρ`).
Route: `gradient (confinement a) x = a • x` (Mathlib `HasGradientAt` via `hasStrictFDerivAt_norm_sq`),
`⟪x, ∇f⟫ = fderiv f x x`, and the drift `-F - a x` of `quadraticGradientDyn`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07a_grad_conf (a : ℝ) (x : Euc d) :
    gradient (confinement a) x = a • x := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := h1.const_mul (a / 2)
  have hg : HasGradientAt (confinement a) (a • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h2 using 1
    · funext y
      simp only [confinement]
      ring
    · ext v
      simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
      ring
  exact hg.gradient

theorem r26t8a_f07a_inner_grad (f : Euc d → ℝ) (x : Euc d) :
    inner ℝ x (gradient f x) = fderiv ℝ f x x := by
  unfold gradient
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

theorem r26t8a_f07a_drift (a beta : ℝ) (rho : Euc d → ℝ) (x : Euc d) :
    (critCoeff d a beta rho).drift 0 x = -(forceMean rho x) - a • x := by
  simp only [critCoeff, quadraticGradientDyn, WholeDyn.coeff, meanFieldDriftW, forceMean,
    criticalS, r26t8a_f05b_matVec_neg, r26t8a_f07a_grad_conf]

end HRS.MS.R26T8A

end
