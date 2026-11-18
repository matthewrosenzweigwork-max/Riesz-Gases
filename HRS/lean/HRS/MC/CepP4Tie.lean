import HRS.MC.CepP4
import HRS.MC.CepaSpec

/-!
Tie for packet P4: the proof `HRS.MC.CepP4.cep_P4_time_slices_proof` has the statement of the frozen spec
`HRS.MC.Cepa.cep_P4_time_slices` (the sorry warnings from the spec are expected here).
-/

example := (@HRS.MC.CepP4.cep_P4_time_slices_proof : type_of% @HRS.MC.Cepa.cep_P4_time_slices)
