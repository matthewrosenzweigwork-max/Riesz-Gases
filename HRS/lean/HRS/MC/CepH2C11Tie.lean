import HRS.MC.CepH2C11
import HRS.MC.CepH4Spec

/-!
# Tie for packet CEPH2C11: the proof has the statement of `cep_H2_c11_cylinder_entropy`.
-/

example := (@HRS.MC.CepH2C11.cep_H2_c11_cylinder_entropy_proof :
  type_of% @HRS.MC.CepH4.cep_H2_c11_cylinder_entropy)
