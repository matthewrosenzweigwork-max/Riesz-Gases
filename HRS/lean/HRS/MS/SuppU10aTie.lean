import HRS.MS.SuppU10a
import HRS.Whole.AppendixBField

/-! Tie of `HRS.MS.U10.limit_field_rd_gaussian_proof` to the frozen statement
`HRS.Whole.limit_field_rd_gaussian` (the warning about the unproved frozen statement is expected). -/

example := (@HRS.MS.U10.limit_field_rd_gaussian_proof : type_of% @HRS.Whole.limit_field_rd_gaussian)
