import HRS.MS.SA16TransferDefs

/-!
# S.A.16 T3: `dense_dissipativity_extension`

The function `x ↦ D(N^p)(x)[A x] - p C N(x)^p` is continuous, so its nonpositive sublevel set is closed;
it contains the dense set, hence everything.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA

theorem dense_dissipativity_extension
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p C : ℝ) (N : X → ℝ) (hN : IsSmoothNorm p N)
    (S : Set X) (hS : Dense S) (A : X →L[ℝ] X)
    (hdiss : ∀ x ∈ S, fderiv ℝ (fun y => (N y)^p) x (A x) ≤ p*C*(N x)^p) :
    ∀ x, fderiv ℝ (fun y => (N y)^p) x (A x) ≤ p*C*(N x)^p := by
  have hNp : Continuous (fun y => (N y)^p) := hN.differentiable.continuous
  have h1 : Continuous (fun x => fderiv ℝ (fun y => (N y)^p) x (A x)) :=
    hN.cont_deriv.clm_apply A.continuous
  have h2 : Continuous (fun x => p*C*(N x)^p) := continuous_const.mul hNp
  have hclosed : IsClosed {x : X | fderiv ℝ (fun y => (N y)^p) x (A x) ≤ p*C*(N x)^p} :=
    isClosed_le h1 h2
  have hsub : S ⊆ {x : X | fderiv ℝ (fun y => (N y)^p) x (A x) ≤ p*C*(N x)^p} := hdiss
  intro x
  have := closure_minimal hsub hclosed
  rw [hS.closure_eq] at this
  exact this (mem_univ x)

end HRS.Whole.AppendixA.Phase2SA16Transfer
