import HRS.ME.SuscPos
import HRS.ME.CondExample
import HRS.MD.EQFrozen29Trans

/-!
# Example 5.11 (`conditioned_example`): proof of the frozen statement

The frozen statement `HRS.conditioned_example` (`HRS/Equilibrium/StaticLimits.lean`) is the conjunction of
the variance positivity `HRS.ME.SuscPos.susc_pos` and the two limits of `HRS.ME.CondExample.cond_example_B`,
whose only analytic input is the centering clause of Theorem 2.9, `HRS.MD.EQFrozen29Trans.centering_transition_proof`.
-/

namespace HRS.ME.CondExampleFinal

theorem conditioned_example_proof {d : ℕ} : type_of% (@HRS.conditioned_example d) := by
  intro s hd hs0 hs β hβ V hV ρ hρ ψ hψ hnc
  exact ⟨HRS.ME.SuscPos.susc_pos hd hs0 hs β hβ V hV ρ hρ ψ hψ hnc,
      HRS.ME.CondExample.cond_example_B hd hs0 hs β hβ V hV ρ hρ ψ hψ
        HRS.MD.EQFrozen29Trans.centering_transition_proof
        (HRS.ME.SuscPos.susc_pos hd hs0 hs β hβ V hV ρ hρ ψ hψ hnc)⟩

end HRS.ME.CondExampleFinal
