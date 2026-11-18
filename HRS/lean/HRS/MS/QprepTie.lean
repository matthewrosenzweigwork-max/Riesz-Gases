import HRS.Whole.Thermal
import HRS.MS.QprepAux14

/-! Tie: `S46.quadratic_preparation_static_proof` and `S46.quadratic_preparation_static_osc_proof` have exactly the types of
the frozen `HRS.Whole.quadratic_preparation_static`, `HRS.Whole.quadratic_preparation_static_osc` (the frozen declarations are
unproved; a warning is expected). -/

example := (@S46.quadratic_preparation_static_proof : type_of% @HRS.Whole.quadratic_preparation_static)

example := (@S46.quadratic_preparation_static_osc_proof :
  type_of% @HRS.Whole.quadratic_preparation_static_osc)
