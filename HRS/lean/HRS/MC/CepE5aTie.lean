import HRS.MC.CepE5a
import HRS.MC.CepaSpec

/-! Tie for packet E5a: `HRS.MC.CepE5a.cep_E5a_pathwise_yosida_proof` has the type of the spec statement. -/

example := (@HRS.MC.CepE5a.cep_E5a_pathwise_yosida_proof : type_of% @HRS.MC.Cepa.cep_E5a_pathwise_yosida)
