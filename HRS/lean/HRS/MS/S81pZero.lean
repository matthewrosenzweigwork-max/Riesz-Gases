import HRS.MS.S81pPathLaw

/-!
# S81P: `S81bW2Zero` reduced to the burn-in coupling alone

`S81W2PathStat` is now a theorem (`s81p_pathStat`), so `S81bW2Zero` (and `critical_whole_W2`) follow from `S81W2Coupling` only.
-/

namespace HRS.Whole.S81P

theorem s81p_zero_of_coupling (hc : HRS.Whole.S81W2.S81W2Coupling) :
    HRS.Whole.BreakdownS81.S81bW2Zero :=
  HRS.Whole.S81W2.s81w2_zero_of_coupling hc s81p_pathStat

theorem s81p_W2_of_coupling (hc : HRS.Whole.S81W2.S81W2Coupling) :
    type_of% @HRS.Whole.critical_whole_W2 :=
  HRS.Whole.S81W2.s81w2_W2_of_coupling hc s81p_pathStat

end HRS.Whole.S81P
