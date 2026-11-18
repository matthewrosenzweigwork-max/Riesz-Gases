import HRS.MC.CepE5c
import HRS.MC.CepaSpec

/-! Tie for packet E5c: `HRS.MC.CepE5c.cep_E5c_cauchy_proof` has the type of the spec statement. -/

example := (@HRS.MC.CepE5c.cep_E5c_cauchy_proof : type_of% @HRS.MC.Cepa.cep_E5c_cauchy)
