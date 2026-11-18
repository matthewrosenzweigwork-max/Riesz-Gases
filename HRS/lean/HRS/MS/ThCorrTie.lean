import HRS.MS.ThCorr
import HRS.Whole.Thermal

/-! Tie: `thermal_corrector_proof` and `thermal_corrector_sobolev_proof` have exactly the types of the frozen
statements `HRS.Whole.thermal_corrector` and `HRS.Whole.thermal_corrector_sobolev` (the frozen declarations are
`unproved`; a warning is expected). -/

example := (@HRS.MS.Tc6.thermal_corrector_proof : type_of% @HRS.Whole.thermal_corrector)

example := (@HRS.MS.Tc6.thermal_corrector_sobolev_proof : type_of% @HRS.Whole.thermal_corrector_sobolev)
