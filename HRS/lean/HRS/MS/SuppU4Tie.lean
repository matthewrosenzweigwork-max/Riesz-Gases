import HRS.MS.SuppU4
import HRS.Whole.Moving

/-! Tie: the proof of `mov_scope_infinite_dim_proof` has exactly the type of the frozen statement
`HRS.Whole.mov_scope_infinite_dim` (which is sorried in `HRS/Whole/Moving.lean`; the warning is expected). -/

example := (@mov_scope_infinite_dim_proof : type_of% @HRS.Whole.mov_scope_infinite_dim)
