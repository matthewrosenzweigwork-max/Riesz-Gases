import HRS.MS.R2GenInitAux43
import HRS.MS.R2GenInitStat

/-!
# S10.5 for the stationary trajectory, unconditional

`r2_window_general_initial_stationary`: the stationary statement of `HRS.Whole.r2_window_general_initial` (`ρ = fun _ => ρ_β`), with the window
comparison hypothesis discharged by `s105_compare_stat`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s105_two_thirds_le (hd : 2 ≤ d) : 2 * (d : ℝ) / 3 ≤ d := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem r2_window_general_initial_stationary (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    type_of% (r2_window_general_initial_stationary_of_hcmp hd s hs0 hs a β ha hβ T hT
      (s105_compare_stat hd hs0 (lt_of_lt_of_le hs (s105_two_thirds_le hd)) ha hβ hT)) :=
  r2_window_general_initial_stationary_of_hcmp hd s hs0 hs a β ha hβ T hT
    (s105_compare_stat hd hs0 (lt_of_lt_of_le hs (s105_two_thirds_le hd)) ha hβ hT)

end HRS.Whole
