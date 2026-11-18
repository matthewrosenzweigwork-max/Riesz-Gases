import HRS.MS.DerCorAux2
import HRS.Whole.Thermal

/-! Tie: `HRS.MS.S48.derivative_corrector_proof` has exactly the type of the frozen statement
`HRS.Whole.derivative_corrector` (the frozen declaration is `unproved`; a warning is expected).

Statement adjustments: none.  The integer `J` is chosen `> k + 2 + d/2` (so `J > k + 1 + d/2`), which lets the
Poisson solve be run at regularity `C^{k+2}` as the frozen conclusion `ContDiff ℝ (k + 2) χ` requires. -/

example := (@HRS.MS.S48.derivative_corrector_proof : type_of% @HRS.Whole.derivative_corrector)
