import HRS.MS.WsInitKAux3

/-!
# S21 packet K, final tie: the frozen statement S2.1 (i), `HRS.Whole.whole_space_stationary`

`s21k_init_at` is `S21Init` for all data (packets G and H glued in `WsInitKAux3`); `whole_space_stationary_proof` is the frozen statement,
by `whole_space_stationary_of_init` (WsStatAux39).
-/

noncomputable section

namespace HRS.MS.S21

theorem whole_space_stationary_proof : HRS.Whole.WholeSpaceStationaryStatement :=
  whole_space_stationary_of_init fun d hd s hs0 hsd a β ha hβ T hT => s21k_init_at hd hs0 hsd ha hβ hT

end HRS.MS.S21
