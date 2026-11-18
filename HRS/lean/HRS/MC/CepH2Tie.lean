import HRS.MC.CepH2
import HRS.MC.CepaSpec

/-! Tie for packet CEPH2: `cep_H2_cylinder_entropy_proof` has the statement of the spec theorem (moved out of `CepH2.lean` so that the proof chain imports no spec). -/

example := (@HRS.MC.CepH2.cep_H2_cylinder_entropy_proof : type_of% @HRS.MC.Cepa.cep_H2_cylinder_entropy)
