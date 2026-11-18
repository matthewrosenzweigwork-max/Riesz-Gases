import HRS.MC.CepE1
import HRS.MC.CepaSpec

/-! Tie for packet E1: `HRS.MC.CepE1.cep_E1_chamber_drift_proof` has the type of the spec statement
(the duplicated vocabulary unfolds to the same bodies). -/

example := (@HRS.MC.CepE1.cep_E1_chamber_drift_proof : type_of% @HRS.MC.Cepa.cep_E1_chamber_drift)
