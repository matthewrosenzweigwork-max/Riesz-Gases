import HRS.MS.MovEntAux25

/-!
# S6.6 `mov_entropy`: the tie (conditional on the dissipation inequality)

`HRS.MS.MovEnt.mov_entropy_proof_of_diss : SuperDiss d s → type_of% (@HRS.Whole.mov_entropy d s)`: the frozen statement of
`HRS/Whole/MovingDyn.lean` follows from the single hypothesis `SuperDiss d s` (`HRS/MS/MfeConfAux4.lean`, the whole-space (DISS) of S.B.1,
Layer 1, not proved in the repository).  When `sb1_super_diss : ∀ d s, SuperDiss d s` is available,
`mov_entropy_proof := fun hd hs0 hsd => mov_entropy_proof_of_diss (sb1_super_diss d s) hd hs0 hsd` ties the row.
-/

noncomputable section

namespace HRS.MS.MovEnt

theorem mov_entropy_proof_of_diss {d : ℕ} {s : ℝ} (hDiss : HRS.MS.MfeConf.SuperDiss d s) :
    type_of% (@HRS.Whole.mov_entropy d s) :=
  mov_entropy_of_diss hDiss

end HRS.MS.MovEnt

end
