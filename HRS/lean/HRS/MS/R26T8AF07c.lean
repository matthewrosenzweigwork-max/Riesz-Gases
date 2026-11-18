import HRS.MS.R26T8AL3g

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07c): Laplacian of a `SobSmooth` function

`Δ u x = ∑_i ∂_i ∂_i u x` (coordinates) and `sobolevNormE r (Δ u) ≤ ∑_i sobolevNormE (r+2) u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f07c_lap (u : Euc d → ℝ) (hu : ContDiff ℝ ∞ u) (x : Euc d) :
    Laplacian.laplacian u x =
      ∑ i : Fin d, r26t8a_l3_D i (r26t8a_l3_D i u) x := by
  have h := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := u)
    (EuclideanSpace.basisFun (Fin d) ℝ)
  rw [h]
  simp only
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (fun _ : Fin 2 => (EuclideanSpace.single i (1 : ℝ) : Euc d)) =
      ![(EuclideanSpace.single i (1 : ℝ) : Euc d), EuclideanSpace.single i (1 : ℝ)] := by
    funext j
    fin_cases j <;> rfl
  have e2 := congrFun (r26t8a_l3_iter_eq i u hu 2) x
  simp only [EuclideanSpace.basisFun_apply]
  rw [← hm, ← e2]
  rfl

end HRS.MS.R26T8A

end
