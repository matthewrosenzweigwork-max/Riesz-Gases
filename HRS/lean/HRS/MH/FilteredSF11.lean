import HRS.MH.FilteredSF8
import HRS.Main.GFFinal5
import HRS.Dynamics.SetupFiltered

/-!
# Filtered packet SF11: `general_fluctuation_filtered` (gradient case)

Copy-with-edits of `HRS.GF.gff_general_fluctuation` (`HRS/Main/GFFinal5.lean`): `gff_core` is replaced by the
filter-order core `sf8_gff_core_L` with the order `L`, and the hypothesis `hγL` is weakened to `d/2 + 1 + 2L < γ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **SF11**: `general_fluctuation_filtered`, gradient clause, with the heat-filter order `L`. -/
theorem general_fluctuation_filtered_proof : type_of% @HRS.GeneralSetup.general_fluctuation_filtered := by
  intro d b L hL hγL
  have hγL' : (d : ℝ) / 2 + 1 + 2 * (L : ℝ) < (b.γ : ℝ) :=
    lt_of_le_of_lt
      (by linarith [le_max_left (2 * (L : ℝ)) ((⌈((d : ℝ) - b.s) / 2⌉ : ℝ) + 1)])
      (lt_of_le_of_lt (le_max_right _ _) hγL)
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_proof b
  obtain ⟨C₀min, hcore⟩ := sf8_gff_core_L b (-1) (fun S => S.PosDensityWith b.c) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K L hL hγL'
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

end HRS.MH.FilteredP
