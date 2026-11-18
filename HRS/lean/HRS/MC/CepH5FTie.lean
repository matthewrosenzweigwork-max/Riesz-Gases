import HRS.MC.CepH5Spec
import HRS.MC.CepH5FFilt

/-! Tie for packet F: the relocated proof has exactly the statement of the spec lemma. -/

example := (@HRS.MC.CepH5Pf.h5_cond_filtered_proof : type_of% @HRS.MC.CepH5.h5_cond_filtered)
