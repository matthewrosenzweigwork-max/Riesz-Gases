import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 evolution-companion core: self-contained definitions

Literal copy of `wrep` from `skeleton/cores/SA16-EVOLUTION-COMPANIONS.lean` (the remaining definitions
there need the stochastic development and are not copied here).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA

def wrep (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : WmpSpace d k p) (x : Euc d) : ℝ :=
  ((G : WLp d k p) : Euc d → WIndex d k → ℝ) x (wZero d k)

end HRS.Whole.AppendixA.Phase2SA16Evolution
