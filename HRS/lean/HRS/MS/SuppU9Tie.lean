import HRS.MS.SuppU9
import HRS.Whole.Orbits

/-! Tie: `orbit_maximal_proof` has exactly the type of the frozen statement `HRS.Whole.orbit_maximal`
(sorried in `HRS/Whole/Orbits.lean`; the warning is expected). -/

example := (@HRS.MS.U9.orbit_maximal_proof : type_of% @HRS.Whole.orbit_maximal)
