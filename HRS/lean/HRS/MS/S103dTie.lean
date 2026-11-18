import HRS.MS.S103dLip2

/-!
# S10.3 (S103D), part 3: the unconditional tie to the frozen `HRS.Whole.r2_window_orbits`

Namespace `HRS.MS.R2WinOrbNL`.  `s103d_r2_window_orbits_proof : type_of% @HRS.Whole.r2_window_orbits`: the frozen statement (ED13/ED14 form, class constants `c₁ C₁` first,
then `ε_*`), proved from `s103d_tie` (TRE3) with its residual premise `S103cRhoPrimeUCsmall` discharged by `s103d_rhoPrimeUCsmall` (S103dLip2).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace HRS.MS.R2WinOrbNL

theorem s103d_r2_window_orbits_proof : type_of% @HRS.Whole.r2_window_orbits :=
  fun {_} hd s hs0 hs a β ha hβ T hT =>
    s103d_tie hd s hs0 hs a β ha hβ T hT (s103d_rhoPrimeUCsmall hd hs0 hs ha hβ)

end HRS.MS.R2WinOrbNL

end
