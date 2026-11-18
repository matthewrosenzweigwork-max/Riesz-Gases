import HRS.MS.R26T8AF00

/-!
# S8.2 observed-time layer, packet T8A.F05 (helper 05b): the nonlocal term at the critical coefficients

For the critical coefficients `critCoeff d a β ρ` (interaction matrix `-1`, convolution exponent `s = d/2`),
the nonlocal term `oneJ` is the sum of the forces `forceConv j (ρ ∂_j f)`:
`oneJ C f x = ∑_j (T_j (ρ ∂_j f)) x`, with `T_j` the critical convolution of F00.
Route: unfold `generatorW`, use `Torus.matVec (-1)ᵀ v = -v`, `gradient f y j = fderiv f y e_j`, and
`convGradConvW G (-g) = -convGradConvW G g` (pointwise negation of the integrand).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f05b_matVec_neg (v : Euc d) :
    Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem r26t8a_f05b_grad_comp (f : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    gradient f y j = fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ)) := by
  have h2 := EuclideanSpace.inner_single_left (𝕜 := ℝ) j (1 : ℝ)
    ((InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f y))
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply] at h2
  unfold gradient
  simpa using h2.symm

theorem r26t8a_f05b_convGrad_neg (G : Euc d → Euc d) (g : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun y => -(g y)) x = -(convGradConvW G g x) := by
  unfold convGradConvW
  rw [← integral_neg]
  congr 1
  funext y
  split_ifs <;> module

theorem r26t8a_f05b_oneJ_eq (a beta : ℝ) (rho f : Euc d → ℝ) (x : Euc d) :
    oneJ (critCoeff d a beta rho) f x =
      ∑ j : Fin d, r26t8a_forceConv j
        (fun y => rho y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) x := by
  have key : ∀ j : Fin d, (fun y => (critCoeff d a beta rho).ρ 0 y *
      (Torus.matVec (critCoeff d a beta rho).M.transpose (gradient f y)) j) =
      fun y => -(rho y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) := by
    intro j
    funext y
    simp [critCoeff, quadraticGradientDyn, WholeDyn.coeff, r26t8a_f05b_matVec_neg,
      r26t8a_f05b_grad_comp]
  unfold oneJ generatorW
  simp only [key, r26t8a_f05b_convGrad_neg, PiLp.neg_apply, Finset.sum_neg_distrib, neg_neg]
  simp only [r26t8a_forceConv, criticalS, critCoeff, quadraticGradientDyn, WholeDyn.coeff]
  ring

end HRS.MS.R26T8A

end
