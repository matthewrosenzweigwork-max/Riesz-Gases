import HRS.MC.CepE3
import HRS.MC.CepaSpec

/-! Tie for packet E3: `HRS.MC.CepE3.cep_E3_regularised_sde_proof` has the type of the spec statement
(the duplicated vocabulary unfolds to the same bodies). -/

example := (@HRS.MC.CepE3.cep_E3_regularised_sde_proof : type_of% @HRS.MC.Cepa.cep_E3_regularised_sde)
