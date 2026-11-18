import HRS.ME.Asm417E

/-!
# Relocation of Proposition 4.17 (`HRS.integrated_forcing`)

The frozen statement (after the universe repair ME-R1, `Ω : Type`) is tied to the proof in
`HRS/ME/Asm417E.lean`, following the relocation pattern with `type_of%`.
-/

namespace HRS.ME

theorem integrated_forcing_proof : type_of% @HRS.integrated_forcing :=
  @HRS.ME.integrated_forcing_type_proof

end HRS.ME
