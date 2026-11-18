import HRS.MS.SA12W2U
import HRS.MS.SA12X3C15

/-!
# S.A.12 C5-T06 (SA12X3), part A: dilations of jets, gradient components, jets of the lifted density family
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x3w_pd_smul {c : ℝ} (hc : c ≠ 0) {n : ℕ} (idx : Fin n → Fin d) (g : Euc d → ℝ) (x : Euc d) :
    partialDeriv idx (fun y => g (c • y)) x = c ^ n * partialDeriv idx g (c • x) := by
  unfold partialDeriv
  rw [HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul g hc n x]
  simp

theorem sa12x3w_grad_eq_dir (u : Torus d → ℝ) (j : Fin d) :
    (fun y => Torus.grad u y j) = HRS.KernelGrad.dirTor u (EuclideanSpace.single j (1 : ℝ)) := by
  apply sa12w2_eq_of_lift
  rw [HRS.KernelGrad.lift_dirTor]
  funext y
  have h1 : Torus.lift (fun y => Torus.grad u y j) y = (gradient (Torus.lift u) y) j := by
    exact congrArg (fun v : Euc d => v j) (HRS.KernelD1Aux.lift_grad u y)
  rw [h1]
  have h2 := EuclideanSpace.inner_single_right j (1 : ℝ) (gradient (Torus.lift u) y)
  have h3 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift u) y)
  simp only [one_mul, RCLike.conj_to_real] at h2
  rw [← h2]
  simpa only [gradient] using h3

theorem sa12x3w_matVec_apply (A : Matrix (Fin d) (Fin d) ℝ) (g : Euc d) (i : Fin d) :
    Torus.matVec A g i = ∑ k, A i k * g k := by
  simp [Torus.matVec, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

end HRS.PDE.SA12W2
