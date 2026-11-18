import HRS.MS.MovSchAux16

/-!
# S6.9: the tie `mov_moving_reference_proof`

`HRS.MS.MovSch.mov_moving_reference_proof : type_of% @HRS.Whole.mov_moving_reference` (frozen statement of
`HRS/Whole/MovingDyn.lean`, with the M1/M1b hypotheses `GibbsInvariant`, `GibbsEntropyContraction`).
Clause (1): `s64_ref1` (`MovSchAux6`); (2) density identity `s64_ref2_static` (`MovSchAux9`, `K > 0` from `s64_Zpos`, `MovSchAux7`),
dynamic part `s64_ref2_dyn` (`MovSchAux10`); (3) `s64_ref3` (`MovSchAux16`, via `MovSchAux11`-`15`); (4) `s64_ref4` (`MovSchAux10`).
No hypothesis `IsRegularMFRd` is needed (S6.8 clause (2) is not used).
-/

noncomputable section

namespace HRS.MS.MovSch

open HRS.Whole

theorem mov_moving_reference_proof : type_of% @HRS.Whole.mov_moving_reference := by
  intro d s hd hs0 hsd β q hβ hq ρ₀ hρ a₀
  have hth := hρ.2
  refine ⟨s64_ref1 hd hs0 hsd β q hβ hq ρ₀ hρ a₀, ?_, ?_, ?_⟩
  · intro N hN t ht
    refine ⟨s64_ref2_static hs0 hq hβ hth hN (movShift q a₀ t), ?_⟩
    intro hInv Ω _ P _ X₀ W X hset h0
    exact s64_ref2_dyn hs0 hq hβ hth hN hInv hset h0 t ht
  · intro N hN t ht X hX
    exact s64_ref3 hs0 hq hβ hth hN a₀ t hX
  · intro N hN hCon Ω _ P _ X₀ W X hset t ht
    exact s64_ref4 hs0 hq hβ hth hN hCon hset t ht

end HRS.MS.MovSch

end
