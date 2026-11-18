import HRS.MS.S113EndAux11
import HRS.MS.S113EndAux9

/-!
# S11.3 endpoint (worker S113X), part 12: `r2_moving_Lp` and the S11.4 tie from the three remaining X cores

After parts 10-11 the unproved inputs are exactly
* `S113XSourceIdentity` (X1a, the source identity `R_N^t = -βN(F^{h_u} - E F^{h_u})` for non-translated trajectories),
* `S113XLocalized` (X2, killed Dirichlet diffusion and its removal),
* `S113XLogNormalizer` (X4, only for `γ = 0`; `r2_log_path` (a) for this class).
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

/-- The X cores that remain after the proofs of X1b (exponential moment) and X5 (measurability). -/
def S113XCoresRed (d : ℕ) (s q β γ : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  S113XSourceIdentity d s q β ρ₀ j m εstar r c₀ ∧ S113XLocalized d s q β ρ₀ j m εstar r c₀ ∧
    (γ = 0 → S113XLogNormalizer d s q β ρ₀ j m εstar r c₀)

theorem s113x_r2_moving_Lp_of_red_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XCoresRed d s q β γ ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, hid, hloc, hlog⟩ := hcores
  exact s113x_r2_moving_Lp_of_cores hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL,
      s113x_source_of_identity hd hs0 hs hβ hq hρ hj hC₁ hε hc hc₀ hNL hid, hloc,
      s113x_meas hd hs0 hs hβ hq hρ hj hm hC₁ hε hc₀ hNL, hlog⟩

theorem s113x_r2_moving_moment_transfer_of_red_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XCoresRed d s q β γ ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp' hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113x_r2_moving_Lp_of_red_cores hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs hcores)

end HRS.MS.S113BD
