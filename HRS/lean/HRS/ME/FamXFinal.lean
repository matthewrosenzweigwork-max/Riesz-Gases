/-
# HRS.ME.FamX (packaging): the frozen `HRS.Main.critical_family_path_sup`

`critical_family_path_sup_proved` is tied to the frozen statement by `type_of%`.  The lower bound is
`HRS.ME.FamX.critical_family_path_sup_lower` (`HRS/ME/FamXA.lean`, `N ≥ N₀`), the upper bound is
`HRS.ME.FamV.critical_family_path_sup_upper` (`HRS/ME/FamVFinal.lean`, `N ≥ 2`); the threshold is `max N₀ 2`.
-/
import HRS.ME.FamXA
import HRS.ME.FamVFinal

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamX

theorem critical_family_path_sup_proved {d : ℕ} :
    type_of% (@HRS.Main.critical_family_path_sup d) := by
  intro hd hs0 hsd β hβ k hk m hm T hT ρ hρ
  obtain ⟨c, hc, N₀, hlow⟩ := critical_family_path_sup_lower hd hs0 hsd β hβ k hk m hm T hT ρ hρ
  obtain ⟨C, hC, hup⟩ := HRS.ME.FamV.critical_family_path_sup_upper hd hs0 hsd β hβ k m hm T hT ρ hρ
  refine ⟨c, C, hc, hC, max N₀ 2, fun N hN Ω _ P _ X₀ W X hflow hfilt Ω' _ P' _ Z hZ => ⟨?_, ?_⟩⟩
  · exact hlow N (le_trans (le_max_left _ _) hN) Ω P X₀ W X hflow hfilt Ω' P' Z hZ
  · exact hup N (le_trans (le_max_right _ _) hN) Ω P X₀ W X hflow hfilt Ω' P' Z hZ

end HRS.ME.FamX
