import HRS.MS.SA12X3C15D

/-!
# S.A.12 C15 (SA12X3), part E: a cutoff pair from a uloc cutoff
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_cutoffPair {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) : ∃ χh : Euc d → ℝ, IsCutoffPair χ χh := by
  let f : ContDiffBump (0 : Euc d) := ⟨6, 7, by norm_num, by norm_num⟩
  refine ⟨⇑f, hχ, f.contDiff, f.hasCompactSupport, ?_, fun x => ⟨f.nonneg, f.le_one⟩, fun x hx => ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    show dist x 0 < 8
    have : dist x 0 ≤ 7 := hx
    linarith
  · exact f.one_of_mem_closedBall (by simpa using hx)

end HRS.MH.AdjointRd.Phase2SA12Construction
