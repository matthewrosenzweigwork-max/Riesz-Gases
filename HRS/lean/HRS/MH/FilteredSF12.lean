import HRS.MH.FilteredSF8
import HRS.Main.GFFinal5
import HRS.Dynamics.SetupFiltered

/-!
# Filtered packet SF12: `general_fluctuation_matrix_filtered` (general-matrix case)

Copy-with-edits of `HRS.GF.gff_general_fluctuation_matrix` (`HRS/Main/GFFinal5.lean`): `gff_core` is replaced by the
filter-order core `sf8_gff_core_L` with the order `L`, and the hypothesis `hγL` is weakened to `d/2 + 1 + 2L < γ`
(the martingale and covariation live at level `S.γ`, as in SF11).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **SF12**: `general_fluctuation_matrix_filtered`, general-matrix clause, with the heat-filter order `L`. -/
theorem general_fluctuation_matrix_filtered_proof :
    type_of% @HRS.GeneralSetup.general_fluctuation_matrix_filtered := by
  intro d b M hM K L hL hγL
  have hγL' : (d : ℝ) / 2 + 1 + 2 * (L : ℝ) < (b.γ : ℝ) :=
    lt_of_le_of_lt
      (by linarith [le_max_left (2 * (L : ℝ)) ((⌈((d : ℝ) - b.s) / 2⌉ : ℝ) + 1)])
      (lt_of_le_of_lt (le_max_right _ _) hγL)
  obtain ⟨K', hK0, hev⟩ := gf_ev_mat_proof b M hM K
  obtain ⟨C₀min, hcore⟩ := sf8_gff_core_L b M (fun S => S.AdjointInput M K) (fun S => (S.γ : ℝ) + 2)
    (fun S => by linarith) (fun S => NegSobolev.embed ((S.γ : ℝ) + 2)) K' L hL hγL'
    (fun S hS hMF hAdj N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hAdj N
      exact ⟨EV, hEV, fun x => hEV.j_eq x⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hAdj N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hAdj N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

end HRS.MH.FilteredP
