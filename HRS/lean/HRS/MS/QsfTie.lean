import HRS.Whole.Thermal
import HRS.MS.QsfAux3
import HRS.MS.QsfAsm11
import HRS.MS.QsfOsc8

/-! Tie: `S45.exists_gaussian_feature_proof` has exactly the type of the frozen
`HRS.Whole.exists_gaussian_feature` (the frozen declaration is unproved; a warning is expected). -/

example := (@S45.exists_gaussian_feature_proof : type_of% @HRS.Whole.exists_gaussian_feature)

example := (@S45.quadratic_static_field_proof : type_of% @HRS.Whole.quadratic_static_field)

example := (@S45.quadratic_static_field_osc_proof : type_of% @HRS.Whole.quadratic_static_field_osc)
