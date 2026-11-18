import HRS.MS.SA16Y4Cv1
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 (SA16Y4) Id1: the transport pairing of the forward weak term is `∫ F · div(b ψ)`

`sa16y4_movDiv_eq`: for `b : Euc d → Euc d` and `ψ` differentiable, `movDiv (ψ • b) x = sa16so_divFun (b · i) ψ x`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Id1
variable {d : ℕ}

lemma sa16y4_movDiv_eq {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hb : ∀ k, Differentiable ℝ (fun y => b y k)) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : Differentiable ℝ ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    movDiv (fun y => ψ y • b y) x = sa16so_divFun (fun i y => b y i) ψ x := by
  unfold movDiv sa16so_divFun
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiff : DifferentiableAt ℝ (fun y => ψ y • b y) x :=
    (hψ x).smul (differentiableAt_euclidean.2 fun k => hb k x)
  have h1 := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.comp x hdiff.hasFDerivAt
  have h2 : fderiv ℝ (fun y => b y i * ψ y) x =
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp (fderiv ℝ (fun y => ψ y • b y) x) := by
    have : (fun y => b y i * ψ y) = fun y => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (ψ y • b y) := by
      funext y; simp [mul_comm]
    rw [this]; exact h1.fderiv
  rw [h2]; rfl

end Id1

end HRS.Whole.AppendixA.Phase2SA16R
