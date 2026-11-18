import HRS.MC.CepP6
import HRS.MC.CepaSpec

/-!
Tie for packet P6: the proof `HRS.MC.CepP6.cep_P6_selected_law_smoothing_proof` has the statement of the frozen spec
`HRS.MC.Cepa.cep_P6_selected_law_smoothing` (the sorry warnings from the spec are expected here).
-/

example := (@HRS.MC.CepP6.cep_P6_selected_law_smoothing_proof : type_of% @HRS.MC.Cepa.cep_P6_selected_law_smoothing)
