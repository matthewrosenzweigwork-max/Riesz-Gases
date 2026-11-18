import HRS.MC.CepH4Fin
import HRS.MC.CepaSpec

/-!
Tie for packet CEPH4FIN: `HRS.MC.CepH4Fin.cep_H4_single_component_proof` has the statement of the specification
`HRS.MC.Cepa.cep_H4_single_component`.
-/

example := (@HRS.MC.CepH4Fin.cep_H4_single_component_proof :
  type_of% @HRS.MC.Cepa.cep_H4_single_component)
