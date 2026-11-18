import HRS.MS.S81FinC
import HRS.MS.S81FinS
import HRS.MS.R26T8AFinal2

/-!
# S8.1 final composition, part 4: the three `critical_whole_*` declarations from P29 alone

`r26t8a_weighted_critical_forcing_of_P29 (S8.2, O01 + B09 + B10 + C15 adapter)` feeds parts 1-3.  The only open input is the
statement `r26t8a_P29_stmt` of packet P29 (`r26t8a_weighted_pair_corrector`).
-/

set_option autoImplicit false
noncomputable section
namespace HRS.Whole.S81Fin

theorem s81fin_W2_of_P29 (hP29 : HRS.MS.R26T8A.r26t8a_P29_stmt) : type_of% @HRS.Whole.critical_whole_W2 :=
  s81fin_W2_of_forcing (HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_of_P29 hP29)

theorem s81fin_constants_of_P29 (hP29 : HRS.MS.R26T8A.r26t8a_P29_stmt) :
    type_of% @HRS.Whole.critical_whole_constants :=
  s81fin_constants_of_forcing (HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_of_P29 hP29)

theorem s81fin_smooth_of_P29 (hP29 : HRS.MS.R26T8A.r26t8a_P29_stmt) :
    type_of% @HRS.Whole.critical_whole_smooth :=
  s81fin_smooth_of_forcing (HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_of_P29 hP29)

end HRS.Whole.S81Fin

end
