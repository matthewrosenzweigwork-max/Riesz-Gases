import HRS.MC.CepE2Props
import HRS.MC.CepH4Spec

/-! Tie for packet CEPE2PROPS.  The spec's `cep_Yosida` is a different (nominal) structure from the duplicated
`HRS.MC.CepE2.cep_Yosida`; the first spec statement is therefore obtained by repackaging the four fields.  All other
vocabulary (`Ch`, `cep_Alcove`, `cep_chamberPot`, `cep_diag`) unfolds to identical bodies. -/

example : type_of% @HRS.MC.CepH4.cep_E2_envelope_props := by
  intro a ha N _
  obtain ⟨J, Φn, hY, h1, h2, h3, h4, h5, h6⟩ := HRS.MC.CepE2Props.cep_E2_envelope_props_proof a ha N
  exact ⟨J, Φn, ⟨hY.mem, hY.force, hY.lip, hY.yosida⟩, h1, h2, h3, h4, h5, h6⟩

example := (@HRS.MC.CepE2Props.cep_H4_potential_conf_proof : type_of% @HRS.MC.CepH4.cep_H4_potential_conf)
