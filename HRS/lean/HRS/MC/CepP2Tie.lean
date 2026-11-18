import HRS.MC.CepP2
import HRS.MC.CepaSpec

/-!
Tie for packet P2: the proof `HRS.MC.CepP2.cep_P2_parabolic_weyl_proof` has the statement of the frozen spec
`HRS.MC.Cepa.cep_P2_parabolic_weyl` (the sorry warnings from the spec are expected here).
-/

example := (@HRS.MC.CepP2.cep_P2_parabolic_weyl_proof : type_of% @HRS.MC.Cepa.cep_P2_parabolic_weyl)
