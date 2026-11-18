import HRS.MS.S113EndAux8
import HRS.MS.R2S11Aux15

/-!
# S11.4 tie, conditional on the S11.3 X cores (worker S113X)

`s113x_r2_moving_moment_transfer_of_cores`: `type_of% (r2_moving_moment_transfer ..)` from the same hypothesis as
`s113x_r2_moving_Lp_of_cores` (composition with `HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp'`).
When the X cores are proved, `r2_moving_Lp_proof` and `r2_moving_moment_transfer_proof` are obtained by feeding the cores
for the constants of `mov_nonlinear_proof`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s113x_r2_moving_moment_transfer_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XCores d s q β γ ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp' hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113x_r2_moving_Lp_of_cores hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs hcores)

end HRS.MS.S113BD
