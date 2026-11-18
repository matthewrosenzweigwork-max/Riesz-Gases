import HRS.MS.S81FinW2
import HRS.MS.CritWholeTies

/-!
# S8.1 final composition, part 2: `critical_whole_constants` from `weighted_critical_forcing`
-/

set_option autoImplicit false
noncomputable section
namespace HRS.Whole.S81Fin

theorem s81fin_constants_of_forcing (hforce : type_of% @HRS.Whole.weighted_critical_forcing) :
    type_of% @HRS.Whole.critical_whole_constants :=
  HRS.Whole.S81b.s81d_constants_of_W2 (s81fin_W2_of_forcing hforce)

end HRS.Whole.S81Fin

end
