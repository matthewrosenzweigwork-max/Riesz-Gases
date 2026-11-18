import HRS.MH.AdjointRdDefs

/-!
# S.A.12 limit core: the compactness weight and measure (definitions of `SA12-LIMIT`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

def compactWeight (d : ℕ) (x : Euc d) : ℝ :=
  jbracket x ^ (-((d : ℝ) + 3))
def compactMeasure (d : ℕ) : Measure (Euc d) :=
  volume.withDensity (fun x => ENNReal.ofReal (compactWeight d x))
abbrev CompactL2 (d : ℕ) := Lp ℝ 2 (compactMeasure d)

end HRS.MH.AdjointRd.Phase2SA12Limit
