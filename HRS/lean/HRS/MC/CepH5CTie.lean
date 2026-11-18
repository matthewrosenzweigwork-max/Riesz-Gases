import HRS.MC.CepH5Spec
import HRS.MC.CepH5C1
import HRS.MC.CepH5C2
import HRS.MC.CepH5C3

/-! Tie for packet C (components): the `_proof` theorems have the types of the spec lemmas. -/

example := (@HRS.MC.CepH5Pf.h5Comp_isOpen_proof : type_of% @HRS.MC.CepH5.h5Comp_isOpen)
example := (@HRS.MC.CepH5Pf.h5Comp_disjoint_proof : type_of% @HRS.MC.CepH5.h5Comp_disjoint)
example := (@HRS.MC.CepH5Pf.h5Comp_iUnion_proof : type_of% @HRS.MC.CepH5.h5Comp_iUnion)
example := (@HRS.MC.CepH5Pf.h5Comp_nonempty_proof : type_of% @HRS.MC.CepH5.h5Comp_nonempty)
