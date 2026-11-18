import HRS.MS.SA16SHw4

/-!
# S.A.16 (SA16S) Hw5: `sa16r_lap` is Mathlib's Laplacian
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hw5
variable {d : ℕ}

lemma sa16sw_lap_eq {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) : sa16r_lap f = Laplacian.laplacian f := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  funext x
  unfold sa16r_lap
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [h1, iteratedFDeriv_two_apply]
  simp

end Hw5

end HRS.Whole.AppendixA.Phase2SA16R
