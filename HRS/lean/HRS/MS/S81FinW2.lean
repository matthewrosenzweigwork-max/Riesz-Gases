import HRS.MS.S81qOld
import HRS.MS.S81pZero

/-!
# S8.1 final composition, part 1: `critical_whole_W2` from `weighted_critical_forcing`

`weighted_critical_forcing -> S81PBlocks (s81q_blocks) -> S81W2Coupling (s81p_coupling_of_blocks)
 -> critical_whole_W2 (s81p_W2_of_coupling, with the proved path-law stationarity)`.
-/

set_option autoImplicit false
noncomputable section
namespace HRS.Whole.S81Fin

theorem s81fin_W2_of_forcing (hforce : type_of% @HRS.Whole.weighted_critical_forcing) :
    type_of% @HRS.Whole.critical_whole_W2 :=
  HRS.Whole.S81P.s81p_W2_of_coupling
    (HRS.Whole.S81P.s81p_coupling_of_blocks (HRS.Whole.S81Q.s81q_blocks hforce))

end HRS.Whole.S81Fin

end
