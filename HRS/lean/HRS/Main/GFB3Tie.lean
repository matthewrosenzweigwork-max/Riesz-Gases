import HRS.Main.GFB3Aux13

/-!
# Packet GFB3: tie of `gf_pair_identification` (repaired statement with `hZm`, 2026-10-17, ISSUES GFB3)
-/

noncomputable section

namespace HRS.GF

variable {d : ℕ}

theorem gf_pair_identification_proof : type_of% @HRS.GF.gf_pair_identification :=
  @gfb3_pair_identification_aem

example := (@gf_pair_identification_proof : type_of% @HRS.GF.gf_pair_identification)

end HRS.GF
