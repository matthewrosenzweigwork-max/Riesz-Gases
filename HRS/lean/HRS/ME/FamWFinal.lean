/-
# HRS.ME.FamW (packaging): the frozen `HRS.Main.critical_family_sharpness`

`critical_family_sharpness_proved` is tied to the frozen statement by `type_of%`.  It combines the upper bound
`HRS.ME.FamV.critical_family_sharpness_upper` (`HRS/ME/FamVE.lean`, valid for `N ≥ 2`) with the lower bound
`HRS.ME.FamW.critical_family_sharpness_lower` (`HRS/ME/FamWE.lean`, valid for `N ≥ N₀`), at the threshold
`max N₀ 2`, for each fixed `β`.
-/
import HRS.ME.FamWE
import HRS.ME.FamVE

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamW

theorem critical_family_sharpness_proved {d : ℕ} :
    type_of% (@HRS.Main.critical_family_sharpness d) := by
  intro hd βm βp hβm hββ k hk β hβ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨c, hc, N₀, hlow⟩ := critical_family_sharpness_lower hd hβ0 k hk
  obtain ⟨C, hC, hup⟩ := HRS.ME.FamV.critical_family_sharpness_upper hd hs0 hsd β hβ0 k
  refine ⟨c, C, hc, hC, max N₀ 2, fun ρ hρ N hN => ⟨hlow ρ hρ N (le_trans (le_max_left _ _) hN),
    hup ρ hρ N (le_trans (le_max_right _ _) hN)⟩⟩

end HRS.ME.FamW
