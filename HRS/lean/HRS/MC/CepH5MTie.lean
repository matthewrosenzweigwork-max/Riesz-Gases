import HRS.MC.CepH5Spec
import HRS.MC.CepH5MFlow
import HRS.MC.CepH5MCond
import HRS.MC.CepH5MMixFinal

noncomputable section

example := (@HRS.MC.CepH5Pf.h5_flow_of_ac_proof : type_of% @HRS.MC.CepH5.h5_flow_of_ac)
example := (@HRS.MC.CepH5Pf.h5_cond_brownian_proof : type_of% @HRS.MC.CepH5.h5_cond_brownian)
example := (@HRS.MC.CepH5Pf.h5_cond_indep_proof : type_of% @HRS.MC.CepH5.h5_cond_indep)
example := (@HRS.MC.CepH5Pf.h5_selectedLaw_mixture_proof : type_of% @HRS.MC.CepH5.h5_selectedLaw_mixture)
