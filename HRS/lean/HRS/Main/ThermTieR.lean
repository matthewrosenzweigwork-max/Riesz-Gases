import HRS.Main.ThermFinal

/-! Tie of the THERM proof to the repaired frozen statement `HRS.Main.thermalization_recentered`
(statement repair THERM-R, ISSUES.md 2026-10-17: `hm : d/2 < m`). -/

namespace HRS
namespace Main

example := (@thermalization_recentered_hm_proof : type_of% @HRS.Main.thermalization_recentered)

theorem thermalization_recentered_proof : type_of% @HRS.Main.thermalization_recentered :=
  @thermalization_recentered_hm_proof

end Main
end HRS
