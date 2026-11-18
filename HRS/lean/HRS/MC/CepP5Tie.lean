import HRS.MC.CepaSpec
import HRS.MC.CepP5

/-!
Tie for packet P5 (repaired statement): the proof `HRS.MC.CepP5.cep_P5_forward_equation_proof` has the statement of the
frozen spec `HRS.MC.Cepa.cep_P5_forward_equation` (which carries the extra hypothesis `hf0`). The core
`HRS.MC.CepP5.cep_P5_forward_equation_core` does not use the hypothesis `0 < D.invβ`, so it is dropped here.
-/

noncomputable section

namespace HRS.MC.CepP5

theorem cep_P5_forward_equation_proof : type_of% @HRS.MC.Cepa.cep_P5_forward_equation := by
  intro Ω mΩ P d N _ hN _ ℱ W' D _ hV T hT X₀ W X hX hF f hfs hf0 hρ
  exact cep_P5_forward_equation_core hN hV hT hX hF hfs hf0 hρ

end HRS.MC.CepP5

example := (@HRS.MC.CepP5.cep_P5_forward_equation_proof : type_of% @HRS.MC.Cepa.cep_P5_forward_equation)
