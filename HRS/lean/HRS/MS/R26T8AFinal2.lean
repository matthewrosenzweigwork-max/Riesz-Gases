import HRS.MS.R26T8AFinal
import HRS.MS.R26T8AC15

/-!
# S8.2 T8A: the final composition with the C15 adapter plugged in

`r26t8a_weighted_critical_forcing_of_P29 hP29 : type_of% @HRS.Whole.weighted_critical_forcing`: only packet P29 remains.
-/

noncomputable section
set_option autoImplicit false
namespace HRS.MS.R26T8A

theorem r26t8a_weighted_critical_forcing_of_P29 (hP29 : r26t8a_P29_stmt) :
    type_of% @HRS.Whole.weighted_critical_forcing :=
  r26t8a_weighted_critical_forcing_final
    (fun d hd a beta C0 ha hbeta q hq => r26t8a_pointwise_pin_comparison d hd a beta C0 ha hbeta q hq) hP29

end HRS.MS.R26T8A

end
