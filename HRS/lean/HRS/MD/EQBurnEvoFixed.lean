import HRS.MD.EQBurnDefs
import HRS.MD.EQRemSetup
import HRS.Main.T25PAux18
import HRS.Uniform.Q48bAux1
import HRS.Sections.Q41Aux14

/-!
# EQ-BURN P1 (chunk D): `eq_evo_fixed`, the evolution package at fixed `β`

Proof of the frozen statement `HRS.MD.EQBurn.eq_evo_fixed` (relocation; see `EQBurnEvoFixedTie.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnEvoFixed

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQBurn

variable {d : ℕ}

theorem eq_evo_fixed_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 < T) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ EvoPkg d s hs0 hsd V β β hβ m K c T Cmax := by
  by_cases hex : ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρ
  · obtain ⟨ρ0, h0⟩ := hex
    obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV h0
    have hρs : SmoothPosDensity ρ0 := ⟨h0.1, hsm, hpos⟩
    have htr : IsSmoothPositiveTrajectory d s β V ρ0 (fun _ => ρ0) :=
      { hs0 := hs0, hsd := hsd, hβ := hβ, V_smooth := hV, init := hρs,
        global := fun K _ => ⟨fun _ => PDE.coeffOf ρ0,
          HRS.Uniform.Q48b.q48b_isMFSolutionHK (by omega) s hs0 hsd β hβ V hV ρ0 h0 hρs.smooth
            hρs.pos K,
          fun t _ => congrFun (HRS.Uniform.Q48b.q48b_mfPath_const ρ0 hρs.smooth) t⟩ }
    obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hT'⟩ := HRS.T25P.t25p_ev_pkg hd htr m
    obtain ⟨Cmax, hC, hev⟩ := hT' T hT
    refine ⟨Cr, cr, Cmax, hCr.le, hcr, hC, ?_⟩
    intro β' hβ' ρ' hρ'
    have hbb : β' = β := le_antisymm hβ'.2 hβ'.1
    subst hbb
    obtain ⟨hpos', hsm'⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ'
    have hρeq : ρ' = ρ0 :=
      PDE.MFThermal.thermal_unique hd s hs0 hsd β' hβ V ρ0 ρ' h0
        (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos hρ'
        (HRS.StaticLimitAux.continuous_of_smooth hsm') hpos'
    subst hρeq
    exact ⟨Vev, hev, hdual⟩
  · refine ⟨1, 1, 0, zero_le_one, one_pos, le_rfl, ?_⟩
    intro β' hβ' ρ' hρ'
    have hbb : β' = β := le_antisymm hβ'.2 hβ'.1
    subst hbb
    exact absurd ⟨ρ', hρ'⟩ hex

end HRS.MD.EQBurnEvoFixed
