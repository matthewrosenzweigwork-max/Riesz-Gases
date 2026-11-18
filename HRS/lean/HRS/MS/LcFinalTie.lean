import HRS.MS.LcFinal
import HRS.Whole.Adjoint

/-! Tie: `local_decay_proof` has exactly the type of the frozen statement `HRS.Whole.local_decay`
(the frozen declaration is `unproved`; a warning is expected). -/

example := (@HRS.MS.Lc.local_decay_proof : type_of% @HRS.Whole.local_decay)
