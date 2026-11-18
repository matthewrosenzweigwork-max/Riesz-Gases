import HRS.MS.SuppU2
import HRS.Whole.Adjoint

/-! Tie: `far_derivatives_proof` has exactly the type of the frozen statement `HRS.Whole.far_derivatives`
(the frozen declaration is `unproved`; a warning is expected). -/

example := (@HRS.Whole.far_derivatives_proof : type_of% @HRS.Whole.far_derivatives)
