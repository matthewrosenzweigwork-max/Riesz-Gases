import HRS.Whole.Thermal
import HRS.MS.TiltAux14

/-! Tie: `S47.tilt_static_proof`, `S47.tilt_static_osc_proof`, `S47.tilt_static_mean_field_proof` have exactly the types of the
frozen `HRS.Whole.tilt_static`, `HRS.Whole.tilt_static_osc`, `HRS.Whole.tilt_static_mean_field` (the frozen declarations are
unproved; a warning is expected).  No statement was adjusted.  The proofs are re-exported as `HRS.MS.Tilt.*_proof`. -/

example := (@S47.tilt_static_proof : type_of% @HRS.Whole.tilt_static)

example := (@S47.tilt_static_osc_proof : type_of% @HRS.Whole.tilt_static_osc)

example := (@S47.tilt_static_mean_field_proof : type_of% @HRS.Whole.tilt_static_mean_field)

namespace HRS.MS.Tilt

theorem tilt_static_proof : type_of% @HRS.Whole.tilt_static := @S47.tilt_static_proof

theorem tilt_static_osc_proof : type_of% @HRS.Whole.tilt_static_osc := @S47.tilt_static_osc_proof

theorem tilt_static_mean_field_proof : type_of% @HRS.Whole.tilt_static_mean_field :=
  @S47.tilt_static_mean_field_proof

end HRS.MS.Tilt
