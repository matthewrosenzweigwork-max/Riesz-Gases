import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Sum3

/-!
# S8.2 observed-time layer, packet T8A.R00: native smooth-kernel global pole majorant

The short-range pole `q` of the heat cutoff satisfies `q z ≤ K (1 + min(1,|z|)^(-criticalS d))` for `z ≠ 0`.
This is the merged `s82p2_q_le` applied to the structure `ShortRangePole`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_shortRange_bound {d : ℕ} {q : Euc d → ℝ}
    (hq : ShortRangePole d q) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Euc d, z ≠ 0 →
      q z ≤ K * (1 + (min 1 ‖z‖) ^ (-criticalS d)) :=
  HRS.MS.S82P2.s82p2_q_le hq

end HRS.MS.R26T8A

end
