import HRS.MS.WsStatAux38

/-!
# S21 packet K-7: the tie of S2.1 (i) to the initial-path input

`whole_space_stationary_of_init`: if the initial-path input `S21Init` (packets G, H: the centred initial orbit path of the stationary
Gibbs law is within `C sqrt(delta_N)` (smooth) and `C delta_N^{3/20}` (`W_1`) of a Gaussian path measure with the static susceptibility
covariance transported by the adjoint orbit) holds for all data, then the frozen statement `HRS.Whole.whole_space_stationary` holds.
Every other ingredient is proved (`WsStatAux2`-`WsStatAux38`).
-/

noncomputable section

namespace HRS.MS.S21

open HRS.Whole

theorem whole_space_stationary_of_init
    (hinit : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (T : ℝ) (hT : 0 < T),
      S21Init d s a β T hT.le) :
    HRS.Whole.WholeSpaceStationaryStatement :=
  HRS.Whole.whole_space_stationary_of_main fun d hd s hs0 hsd a β ha hβ T hT =>
    s21_main_of_init hd hs0 hsd ha hβ hT (hinit d hd s hs0 hsd a β ha hβ T hT)

end HRS.MS.S21
