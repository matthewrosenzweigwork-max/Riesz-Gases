import HRS.MS.SA16EvolDefs
import HRS.MH.AdjointRdDefs
import HRS.MS.SA16TransferFamilyDefs
import HRS.Stochastic.Wiener
import HRS.Stochastic.SDE
import HRS.Stochastic.Ito

/-!
# S.A.16 evolution companions: E1-E4 definitions

Literal copies of `DriftBounds`, `charFlow`, `avgPullback`, `LocalEvolution` from
`skeleton/cores/SA16-EVOLUTION-COMPANIONS.lean` (`wrep` is in `HRS.MS.SA16EvolDefs`, `localTest` in `HRS.MS.SA16TransferFamilyDefs`; the skeleton's `LocalEvolution` has a stray comma in `comp`, fixed to `→`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

def DriftBounds (d k : ℕ) (B : ℝ) (b : ℝ → Euc d → Euc d) : Prop :=
  ContinuousOn (Function.uncurry b) (Ici (0 : ℝ) ×ˢ univ) ∧
    ∀ t : ℝ, 0 ≤ t → ContDiff ℝ k (b t) ∧ ‖b t 0‖ ≤ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (b t) x‖ ≤ B

def charFlow (d : ℕ) (b : ℝ → Euc d → Euc d) (ν : ℝ)
    (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) (x : Euc d) : Euc d :=
  HRS.picardLim (fun r y => -b r y)
    (fun i : Fin d => Real.sqrt (2*ν) • EuclideanSpace.single i (1 : ℝ)) w x t

def avgPullback {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (P : Measure Ω)
    (b : ℝ → Euc d → Euc d) (ν : ℝ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (φ : Euc d → ℝ) (t : ℝ) (x : Euc d) : ℝ :=
  ∫ ξ, φ (Function.invFun (charFlow d b ν (fun r => W r ξ) t) x) ∂P

structure LocalEvolution (d k : ℕ) (p T ν : ℝ) [Fact (2 ≤ p)]
    (b : ℝ → Euc d → Euc d) (S : ℝ → ℝ → WmpSpace d k p →L[ℝ] WmpSpace d k p) : Prop where
  diag : ∀ r ∈ Icc (0 : ℝ) T, S r r=ContinuousLinearMap.id ℝ (WmpSpace d k p)
  comp : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
    (S t s).comp (S s r)=S t r
  cont : ∀ G, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 G)
    {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}
  weak : ∀ r ∈ Icc (0 : ℝ) T, ∀ G,
    IsWeakSol (fun σ => localTest d ν b (r+σ)) (T-r) (wrep d k p G)
      (fun σ => wrep d k p (S (r+σ) r G))

end HRS.Whole.AppendixA.Phase2SA16Evolution
