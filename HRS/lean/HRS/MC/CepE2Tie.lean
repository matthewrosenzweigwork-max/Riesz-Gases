import HRS.MC.CepE2
import HRS.MC.CepaSpec

/-! Tie for packet E2.  The spec's `cep_Yosida` is a `structure`, hence a different (nominal) type from the
duplicated structure `HRS.MC.CepE2.cep_Yosida`; the spec statement is therefore obtained from
`HRS.MC.CepE2.cep_E2_moreau_yosida_proof` by repackaging the four fields.  All other vocabulary (`Ch`,
`cep_Alcove`, `cep_chamberPot`) unfolds to identical bodies. -/

example : type_of% @HRS.MC.Cepa.cep_E2_moreau_yosida := by
  intro a ha N
  obtain ⟨J, Φn, hY, h1, h2, h3⟩ := HRS.MC.CepE2.cep_E2_moreau_yosida_proof a ha N
  exact ⟨J, Φn, ⟨hY.mem, hY.force, hY.lip, hY.yosida⟩, h1, h2, h3⟩
