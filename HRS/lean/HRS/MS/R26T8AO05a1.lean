import HRS.MS.R26T8AD01
import HRS.MH.DualityRdA4

/-!
# S8.2 observed-time layer, packet T8A.O05a (helper 1): particle-wise derivatives of a function on the configuration space

For `F : EucConfig d N → ℝ` differentiable (with `fderiv F` differentiable at `x`), the one-particle Laplacian of
`y ↦ F (update x i y)` at `x i` is `∑_j D²F x (e_{ij}) (e_{ij})`, and `D F x (single i v) = ⟪configGrad F x i, v⟫`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_o05a1_fderiv_update {d N : ℕ} (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N) (i : Fin N) (y : Euc d) :
    fderiv ℝ (fun z => F (Function.update x i z)) y =
      (fderiv ℝ F (Function.update x i y)).comp
        (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d)))) :=
  ((hF _).comp y (hasFDerivAt_update x y)).fderiv

theorem r26t8a_o05a1_lap {d N : ℕ} (F : EucConfig d N → ℝ)
    (hF : ∀ y, HasFDerivAt F (fderiv ℝ F y) y) (x : EucConfig d N)
    (hF2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x) (i : Fin N) :
    Laplacian.laplacian (fun y => F (Function.update x i y)) (x i) =
      ∑ j : Fin d, fderiv ℝ (fderiv ℝ F) x (Pi.single i (EuclideanSpace.single j (1 : ℝ)))
        (Pi.single i (EuclideanSpace.single j (1 : ℝ))) := by
  set L : Euc d →L[ℝ] EucConfig d N :=
    ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d))) with hL
  have hLu : ∀ u, L u = Pi.single i u := by
    intro u; funext k
    by_cases hk : k = i
    · subst hk; simp [hL]
    · simp [hL, Pi.single_apply, hk]
  have hupd : Function.update x i (x i) = x := Function.update_eq_self i x
  have hA : HasFDerivAt (fun z : Euc d => Function.update x i z) L (x i) := hasFDerivAt_update x (x i)
  have h2' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) (Function.update x i (x i)) := by
    rw [hupd]; exact hF2
  have hcomp : HasFDerivAt (fun z => fderiv ℝ F (Function.update x i z))
      ((fderiv ℝ (fderiv ℝ F) x).comp L) (x i) := by
    exact h2'.comp (x i) hA
  have hgd : fderiv ℝ (fun z => F (Function.update x i z)) =
      fun z => (fderiv ℝ F (Function.update x i z)).comp L := funext fun z =>
    r26t8a_o05a1_fderiv_update F hF x i z
  have hderiv : HasFDerivAt (fderiv ℝ (fun z => F (Function.update x i z)))
      ((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip L ∘L
        ((fderiv ℝ (fderiv ℝ F) x).comp L)) (x i) := by
    rw [hgd]
    exact ((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip L).hasFDerivAt.comp (x i) hcomp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  rw [hderiv.fderiv]
  simp [hLu]

end HRS.MS.R26T8A

end
