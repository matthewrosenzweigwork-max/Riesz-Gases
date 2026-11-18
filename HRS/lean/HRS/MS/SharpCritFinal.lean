import HRS.MS.SharpCritTie
import HRS.MS.QsfTie

/-!
# S7.8 critical case: unconditional

`HRS.Whole.S78.sharp_threshold_critical_of_static_field` (conditional on the frozen S4.5 `quadratic_static_field`)
applied to `S45.quadratic_static_field_proof` (S4.5 proved, `HRS/MS/QsfTie.lean`) gives the frozen
`HRS.Whole.sharp_threshold_critical`.  Together with `sharp_threshold_supercritical_proof` this closes S7.8.
-/

namespace HRS.Whole.S78

theorem sharp_threshold_critical_proof : type_of% @HRS.Whole.sharp_threshold_critical :=
  sharp_threshold_critical_of_static_field S45.quadratic_static_field_proof

example := (@sharp_threshold_critical_proof : type_of% @HRS.Whole.sharp_threshold_critical)

end HRS.Whole.S78
