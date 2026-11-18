import HRS.MS.S111X1G2

/-!
# S11.1 `r2_cross_density_exists`: the proof (tie)
-/

noncomputable section

namespace HRS.MS.S111X1

open HRS HRS.Whole

/-- **S11.1 `r2_cross_density_exists`.** -/
theorem r2_cross_density_exists_proof : type_of% @HRS.Whole.r2_cross_density_exists :=
  r2_cross_density_exists_of_exist
    (fun _d hd _s hs0 hs _a _β ha hβ _ρ hρ => exist_of_thermal hd hs0 hs ha hβ hρ)

example := (@r2_cross_density_exists_proof : type_of% @HRS.Whole.r2_cross_density_exists)

end HRS.MS.S111X1
