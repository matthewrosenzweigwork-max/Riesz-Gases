import HRS.MC.CepP3
import HRS.MC.CepaSpec

/-!
Tie for packet P3: the proof `HRS.MC.CepP3.cep_P3_spacetime_density_proof` has the statement of the frozen spec
`HRS.MC.Cepa.cep_P3_spacetime_density` (the sorry warnings from the spec are expected here).
-/

example := (@HRS.MC.CepP3.cep_P3_spacetime_density_proof : type_of% @HRS.MC.Cepa.cep_P3_spacetime_density)
