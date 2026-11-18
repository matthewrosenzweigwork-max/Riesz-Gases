import HRS.MS.MainRdFieldAux15
import HRS.MS.MainRdFieldAux20

/-!
# S.A.6 `main_rd_field` and S.A.7 `rd_field_wasserstein_one/_two`: the proof terms tied to the frozen statement

`main_rd_field_proof : type_of% @HRS.Whole.AppendixA.main_rd_field` (the statement with the approved hypotheses
`FieldAdjointInputRd fd S Kad` and `σ_N e_N → 0`), from `sa6_main` (`MainRdFieldAux15`).
-/

noncomputable section

namespace HRS.MS.MainRdField

theorem main_rd_field_proof : type_of% @HRS.Whole.AppendixA.main_rd_field := sa6_main

theorem rd_field_wasserstein_one_proof : type_of% @HRS.Whole.AppendixA.rd_field_wasserstein_one := sa6_w1

theorem rd_field_wasserstein_two_proof : type_of% @HRS.Whole.AppendixA.rd_field_wasserstein_two := sa6_w2

end HRS.MS.MainRdField
