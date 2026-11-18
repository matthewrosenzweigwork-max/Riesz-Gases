import HRS.MS.SuppU5
import HRS.MS.SuppU5M
import HRS.Whole.AppendixBField

/-! Tie: the proofs `iid_init_field_rd_proof` and `iid_init_field_rd_multitime_proof` have exactly the
types of the frozen statements `HRS.Whole.iid_init_field_rd` and `HRS.Whole.iid_init_field_rd_multitime`
(sorried in `HRS/Whole/AppendixBField.lean`; the warning is expected). -/

example := (@iid_init_field_rd_proof : type_of% @HRS.Whole.iid_init_field_rd)
example := (@iid_init_field_rd_multitime_proof : type_of% @HRS.Whole.iid_init_field_rd_multitime)
