import HRS.MS.SA16TransferDefs
import HRS.MS.SA16CutDefs
import HRS.MS.SA16EvolDefs
import HRS.MS.SA16StrongDefs
import HRS.MH.AdjointRdDefs

/-!
# S.A.16 energy-transfer core: the cutoff family (definitions)

Verbatim copies of `localTest` (`SA16-EVOLUTION-COMPANIONS.lean`, namespace `Phase2SA16Evolution`),
`compatibleTest` (`SA16-COMPATIBLE-CUTOFF.lean`, namespace `Phase2SA16Cutoff`) and of `regularizedWeak`,
`CutoffFamily` (`SA16-ENERGY-TRANSFER.lean`).  A later worker that needs `localTest` or `compatibleTest`
must import this file instead of declaring them again.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

def localTest (d : ℕ) (ν : ℝ) (b : ℝ → Euc d → Euc d)
    (t : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ν*Laplacian.laplacian ψ x-movDiv (fun y => ψ y • b t y) x

end HRS.Whole.AppendixA.Phase2SA16Evolution

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

def compatibleTest (d : ℕ) (δ : ℝ) (C : WholeCoeff d)
    (r : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  q09_c C.s * ∑ i : Fin d, ∑ j : Fin d, C.M j i *
    partialDeriv (fun _ : Fin 1 => j)
      (fun y => C.ρ r y*spliceOdd d (C.s+2-d) δ i ψ y) x

end HRS.Whole.AppendixA.Phase2SA16Cutoff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open Phase2SA16 Phase2SA16Cutoff Phase2SA16Evolution

/-- `WmpSpace` is a closed subspace of a Banach space, hence complete (the instance is not found
through the definition `WmpSpace`). -/
instance sa16x_completeWmp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : CompleteSpace (WmpSpace d m p) := by
  unfold WmpSpace
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def regularizedWeak (d : ℕ) (κc : LpCase) (δ : ℝ) (C : WholeCoeff d)
    (t σ : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  match κc with
  | .sub => weakOp C t σ ψ x
  | _ => localTest d C.ν (fun r => C.drift (t-r)) σ ψ x-compatibleTest d δ C (t-σ) ψ x

structure CutoffFamily (d m : ℕ) (p s t C : ℝ) [Fact (2 ≤ p)]
    (κc : LpCase) (coeff : WholeCoeff d)
    (U : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p) : Prop where
  cont : ∀ n G, ContinuousOn (fun τ => U n τ G) (Icc (0 : ℝ) t)
  initial : ∀ n, U n 0=ContinuousLinearMap.id ℝ (WmpSpace d m p)
  bound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ∀ G, ‖U n τ G‖ ≤ C*Real.exp (C*τ)*‖G‖
  weak : ∀ n G, IsWeakSol (regularizedWeak d κc (cutoffRadius n) coeff t) t
    (wrep d m p G) (fun τ => wrep d m p (U n τ G))
  dense_difference : ∀ φ : Euc d → ℝ, IsCcInfty φ →
    ∀ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] φ →
      ∀ n l : ℕ, ∀ τ ∈ Icc (0 : ℝ) t,
        ‖U n τ G-U l τ G‖ ≤ C*(cutoffRate d s n+cutoffRate d s l)*
          (wNormE (m+2) p φ).toReal

end HRS.Whole.AppendixA.Phase2SA16Transfer
