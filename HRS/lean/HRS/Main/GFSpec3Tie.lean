import HRS.Main.GFSpec3
import HRS.Main.GFB4Aux13
import HRS.Main.GFB4Aux15

/-!
# SPEC-GF3: ties of the two repaired GFSpec3 statements (ISSUES GFB4, repaired 2026-10-17)
-/

noncomputable section

namespace HRS.GF

variable {d : ℕ}

theorem gf_wasserstein_comparison_proof : type_of% @HRS.GF.gf_wasserstein_comparison :=
  @gfb4_wasserstein_comparison_meas

example := (@gf_wasserstein_comparison_proof : type_of% @HRS.GF.gf_wasserstein_comparison)

theorem gf_init_enlargement_proof : type_of% @HRS.GF.gf_init_enlargement :=
  @gfb4_init_enlargement

example := (@gf_init_enlargement_proof : type_of% @HRS.GF.gf_init_enlargement)

end HRS.GF
