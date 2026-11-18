import HRS.MC.CepE4
import HRS.MC.CepaSpec

/-! Tie for packet E4: `HRS.MC.CepE4.cep_E4_L1_bound_proof` has the type of the spec statement. -/

example := (@HRS.MC.CepE4.cep_E4_L1_bound_proof : type_of% @HRS.MC.Cepa.cep_E4_L1_bound)
