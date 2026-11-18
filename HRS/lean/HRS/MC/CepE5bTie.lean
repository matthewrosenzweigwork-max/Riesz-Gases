import HRS.MC.CepaSpec
import HRS.MC.CepE5b

/-! Tie for packet E5b: the repaired spec statement `HRS.MC.Cepa.cep_E5b_yosida_defect` (with `hT : 0 ≤ T`)
has the type of `HRS.MC.CepE5b.cep_E5b_yosida_defect_nonneg`. -/

namespace HRS.MC.CepE5bTie

theorem cep_E5b_yosida_defect_proof : type_of% @HRS.MC.Cepa.cep_E5b_yosida_defect :=
  @HRS.MC.CepE5b.cep_E5b_yosida_defect_nonneg

end HRS.MC.CepE5bTie

example := (@HRS.MC.CepE5bTie.cep_E5b_yosida_defect_proof : type_of% @HRS.MC.Cepa.cep_E5b_yosida_defect)
