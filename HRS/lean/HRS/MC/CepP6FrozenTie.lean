import HRS.MC.CepP6
import HRS.Appendix.CepaFlow

/-!
# Tie of packet P6 to the FROZEN statement `HRS.selected_law_smoothing` (Proposition B.4)

`HRS.MC.CepP6.cep_P6_selected_law_smoothing_proof` has the statement of the frozen `HRS.selected_law_smoothing`.
The only difference is the order of the implicit binders: the frozen statement has `{d N}` before `{Ω mΩ P}`
(section variables of `CepaFlow`), the proof has `{Ω mΩ P}` before `{d N}`, so the tie permutes them.
-/

example : type_of% @HRS.selected_law_smoothing := by
  intro d N Ω mΩ P inst
  exact @HRS.MC.CepP6.cep_P6_selected_law_smoothing_proof Ω mΩ P d N inst
