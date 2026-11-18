import HRS.MC.CepH5Spec
import HRS.MC.CepH5L2b

/-! Tie for packet C (class constancy): `h5_class_constancy_proof` has the type of the spec lemma. -/

example := (@HRS.MC.CepH5Pf.h5_class_constancy_proof : type_of% @HRS.MC.CepH5.h5_class_constancy)
