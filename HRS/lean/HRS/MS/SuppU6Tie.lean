import HRS.MS.SuppU6
import HRS.Whole.CriticalNoise

/-! Tie: the proof `adapted_charts_proof` has exactly the type of the frozen statement
`HRS.Whole.adapted_charts` (sorried in `HRS/Whole/CriticalNoise.lean`; the warning is expected). -/

example := (@adapted_charts_proof : type_of% @HRS.Whole.adapted_charts)
