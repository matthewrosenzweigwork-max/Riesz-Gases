import HRS.MS.AdjDecay
import HRS.Whole.Adjoint

/-! Tie: `adjoint_decay_proof` has exactly the type of the frozen statement `HRS.Whole.adjoint_decay`
(the frozen declaration is `unproved`; a warning is expected). -/

example := (@HRS.MS.AdjDecay.adjoint_decay_proof : type_of% @HRS.Whole.adjoint_decay)
