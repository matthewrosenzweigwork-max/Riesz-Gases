import HRS.MS.ThmCons
import HRS.MS.EucRegH

/-!
# `isAdmissiblePerturbation_thermal` (S3.4 consumer)

The frozen statement `HRS.Whole.isAdmissiblePerturbation_thermal` follows from `cb_admissible_of_smooth` (ThmCons)
and the smoothness of `thermalDensity` (first conjunct of `euc_thermal_regularity_proof`, EucRegH).
-/

namespace HRS.MS.Thm

theorem isAdmissiblePerturbation_thermal_proof :
    type_of% @HRS.Whole.isAdmissiblePerturbation_thermal := by
  intro d s hd hs0 hsd a β ha hβ εstar hε ψ hψ hc h0 hmean
  have hreg := euc_thermal_regularity_proof hd hs0 hsd a β ha hβ
  exact cb_admissible_of_smooth (by omega) hs0 hsd ha hβ hreg.1 εstar hε ψ hψ hc h0 hmean

end HRS.MS.Thm
