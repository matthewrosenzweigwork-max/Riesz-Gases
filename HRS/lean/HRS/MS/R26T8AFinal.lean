import HRS.MS.R26T8AB10
import HRS.MS.R26T8AB09
import HRS.MS.R26T8AO01

/-!
# S8.2 T8A: the final composition `O01 -> B09 -> B10`

`r26t8a_weighted_critical_forcing_final hC15 hP29 : type_of% @HRS.Whole.weighted_critical_forcing`; the only inputs not yet proved are
packets C15 (`r26t8a_C15_stmt`) and P29 (`r26t8a_P29_stmt`).  Once they land:
`weighted_critical_forcing := r26t8a_weighted_critical_forcing_final r26t8a_pointwise_pin_comparison r26t8a_weighted_pair_corrector`.
-/

noncomputable section
set_option autoImplicit false
namespace HRS.MS.R26T8A

theorem r26t8a_weighted_critical_forcing_final (hC15 : r26t8a_C15_stmt) (hP29 : r26t8a_P29_stmt) :
    type_of% @HRS.Whole.weighted_critical_forcing :=
  r26t8a_weighted_critical_forcing
    (r26t8a_scalar_blocks_of_O01 (fun d hd a beta ha hbeta => r26t8a_normal_form_family_of hC15 hP29 d hd a beta ha hbeta))

end HRS.MS.R26T8A

end
