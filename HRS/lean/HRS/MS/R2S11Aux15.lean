import HRS.MS.R2S11Aux14

/-!
# S11.4: `r2_moving_moment_transfer` from the conclusion of S11.3 alone

`s11_moving_moment_transfer_of_Lp'`: the frozen statement `r2_moving_moment_transfer` follows from the conclusion `h113` of
`r2_moving_Lp` (same parameters).  Once S11.3 is proved,
`r2_moving_moment_transfer := s11_moving_moment_transfer_of_Lp' .. (r2_moving_Lp ..)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_moving_moment_transfer_of_Lp' (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (h113 : type_of% (r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs)) :
    type_of% (r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hpos : ∀ x, 0 < ρ₀ x := (HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd hq hβ hρ).2.1
  have hcont : Continuous ρ₀ := by
    obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd hq hβ
    have : ρ₀ = thermalDensity d s q β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd hq hβ hρ
    rw [this]
    exact hT.smooth.continuous
  refine s11_moving_moment_transfer_of_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs ?_ h113
  intro j m εstar r c₀ hm f0 hf0 ρ hρ'
  have hmd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  exact (s11_class_continuous hcont hpos hmd hρ').measurable

end HRS.MS.R2S11
