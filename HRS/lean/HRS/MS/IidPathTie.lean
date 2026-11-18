import HRS.MS.MainRdPathAux30

/-!
# S.A.10 tie: `iid_path_rd` from `iid_path_rd_cond_proof`

`HRS.Whole.AppendixA.iid_path_rd` (frozen statement) is obtained from `iid_path_rd_cond_proof`, whose statement has the
extra hypothesis `∀ N ≥ 1, AEMeasurable (R N).η (R N).P`.  That hypothesis is the field `eta_meas` of `IidSettingRd`
(ED10, approved 2026-10-25).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA

theorem iid_path_rd_proof : type_of% @HRS.Whole.AppendixA.iid_path_rd := by
  intro d s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  obtain ⟨C, hC⟩ := iid_path_rd_cond_proof s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  exact ⟨C, fun C₀ hC₀ S hs hT hinv hH R 𝔈 hid =>
    hC C₀ hC₀ S hs hT hinv hH R 𝔈 hid hid.eta_meas⟩

example := (@iid_path_rd_proof : type_of% @HRS.Whole.AppendixA.iid_path_rd)

end HRS.MS.MainRdPath
