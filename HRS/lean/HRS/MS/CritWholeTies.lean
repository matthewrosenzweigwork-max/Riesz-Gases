import HRS.MS.CritWholeMarginal
import HRS.MS.CritWholeFinal
import HRS.MS.CritWholeW2Shift

/-!
# S8.1 XE (S81d): the ties of `critical_whole_constants` and `critical_whole_smooth`

With the static endpoint `s81d_critical_whole_marginal` now unconditional, the metric constants and the smooth constant follow from the
centered path bound alone (`critical_whole_W2`), which in turn follows from its window-start-zero case `S81bW2Zero`.
-/

set_option autoImplicit false
noncomputable section
open HRS HRS.Whole

namespace HRS.Whole.S81b

/-- `critical_whole_constants` from `critical_whole_W2` (the static endpoint is proved). -/
theorem s81d_constants_of_W2 (hW2 : type_of% @HRS.Whole.critical_whole_W2) :
    type_of% @HRS.Whole.critical_whole_constants :=
  HRS.Whole.BreakdownS81.s81bd_constants_of s81d_critical_whole_marginal hW2

/-- `critical_whole_smooth` from `critical_whole_W2` (the static endpoint is proved). -/
theorem s81d_smooth_of_W2 (hW2 : type_of% @HRS.Whole.critical_whole_W2) :
    type_of% @HRS.Whole.critical_whole_smooth :=
  HRS.Whole.BreakdownS81.s81bd_smooth_of s81d_critical_whole_marginal hW2

/-- `critical_whole_constants` from the window-start-zero case of the centered path bound. -/
theorem s81d_constants_of_zero (h0 : HRS.Whole.BreakdownS81.S81bW2Zero) :
    type_of% @HRS.Whole.critical_whole_constants :=
  s81d_constants_of_W2 (HRS.Whole.BreakdownS81.s81b_W2_of_zero h0)

/-- `critical_whole_smooth` from the window-start-zero case of the centered path bound. -/
theorem s81d_smooth_of_zero (h0 : HRS.Whole.BreakdownS81.S81bW2Zero) :
    type_of% @HRS.Whole.critical_whole_smooth :=
  s81d_smooth_of_W2 (HRS.Whole.BreakdownS81.s81b_W2_of_zero h0)

end HRS.Whole.S81b
