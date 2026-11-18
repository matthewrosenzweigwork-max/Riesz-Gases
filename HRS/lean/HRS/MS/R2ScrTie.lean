import HRS.Whole.Round2
import HRS.MS.R2ScrAux2

/-! Tie: `r2_screened_proof` has exactly the type of the frozen statement `HRS.Whole.r2_screened`
(the frozen declaration is `unproved`; a warning is expected). -/

example := (@HRS.MS.S98.r2_screened_proof : type_of% @HRS.Whole.r2_screened)
