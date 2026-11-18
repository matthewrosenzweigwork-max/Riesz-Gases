import HRS.MS.SuppU3
import HRS.Whole.AppendixALemmas

/-! Tie of `HRS.MS.SuppU3.adjoint_field_kernel_proof` to the frozen statement
`HRS.Whole.AppendixALemmas.adjoint_field_kernel` (the warning about the unproved frozen statement is expected). -/

open HRS.MS.SuppU3 in
example := (@adjoint_field_kernel_proof : type_of% @HRS.Whole.AppendixALemmas.adjoint_field_kernel)
