import HRS.MS.MovEntTie
import HRS.MS.MfeConfAux174

/-!
# S6.6 `mov_entropy`: unconditional

`mov_entropy_of_diss` (MovEntAux25, worker S66b) proves the frozen statement from `SuperDiss d s`; S.B.1 now supplies it for
`d ≥ 2` (`sb1_superDiss_of_movEnt` with `sb1_superMovEnt`, MfeConfAux60/174, workers SB1-SB5), which is the range of
`mov_entropy` (`hd : 2 ≤ d`).
-/

noncomputable section

namespace HRS.MS.MovEnt

theorem mov_entropy_proof : type_of% @HRS.Whole.mov_entropy := by
  intro d s hd hs0 hsd
  exact mov_entropy_of_diss
    (HRS.MS.MfeConf.sb1_superDiss_of_movEnt (by omega) hd hs0 hsd
      (HRS.MS.MfeConf.sb1_superMovEnt (by omega) hs0 hsd)) hd hs0 hsd

example := (@mov_entropy_proof : type_of% @HRS.Whole.mov_entropy)

end HRS.MS.MovEnt
