import HRS.MS.R26T8AP29
import HRS.MS.R26T8AFinal2

/-!
# S8.2 T8A: final tie of the frozen weighted critical forcing endpoint
`r26t8a_weighted_critical_forcing_of_P29 r26t8a_weighted_pair_corrector`: P29 is now proved, so the S8.2 endpoint
`HRS.Whole.weighted_critical_forcing` (as `type_of%`) holds without hypotheses.
-/

noncomputable section
set_option autoImplicit false
namespace HRS.MS.R26T8A

theorem r26t8a_weighted_critical_forcing_tied : type_of% @HRS.Whole.weighted_critical_forcing :=
  r26t8a_weighted_critical_forcing_of_P29 r26t8a_weighted_pair_corrector

end HRS.MS.R26T8A

end
