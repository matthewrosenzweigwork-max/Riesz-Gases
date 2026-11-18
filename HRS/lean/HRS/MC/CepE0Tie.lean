import HRS.MC.CepE0
import HRS.MC.CepaSpec

/-! Tie for packet E0: `HRS.MC.CepE0.cep_E0_sort_proof` has the type of the spec statement
(the duplicated predicate `cepe0_StrictlyOrdered` unfolds to the same body). -/

example := (@HRS.MC.CepE0.cep_E0_sort_proof : type_of% @HRS.MC.Cepa.cep_E0_sort)
