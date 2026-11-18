import HRS.MS.R2WinErrAux18
import HRS.MS.MovEntAux1

/-!
# S11.6 packet C02 (`R26-T8B.C02`): uniform initial round-2 and Gaussian-envelope data for the window class

Prefix `s116_`, namespace `HRS.MS.S116`.  For arbitrary `(εstar, c₁, C₁)`: constants `M, L, Cg, cg` (before the thermal reference and the trajectory) such that
every `IsR2WindowTrajectory` has `IsRound2Density d 0 M L (ρ 0)` (from `s104_hcls_bounds`) and `HasR2GaussianUpper Cg cg (ρ 0)`
(stationary branch: Gaussian bound of the thermal density; nonlinear branch: the ratio clause `ρ 0 ≤ C₁ ρβ` of `IsResultingSolution`).
The thermal reference is unique (`mv0_rho_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_initial_data {d : ℕ} (hd : 2 ≤ d) (a β εstar c₁ C₁ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ M L Cg cg : ℝ, 0 < Cg ∧ 0 < cg ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d 0 a β ρβ →
      ∀ ρ : ℝ → Euc d → ℝ, IsR2WindowTrajectory d 0 a β ρβ εstar c₁ C₁ ρ →
        IsRound2Density d 0 M L (ρ 0) ∧ HasR2GaussianUpper Cg cg (ρ 0) := by
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨M, L, _, _, _, hcls⟩ := HRS.MS.R2WinErr.s104_hcls_bounds hd (s := 0) le_rfl hsd ha hβ εstar c₁ C₁
  have hround : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d 0 a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
      IsR2WindowTrajectory d 0 a β ρβ εstar c₁ C₁ ρ → IsRound2Density d 0 M L (ρ 0) := by
    intro ρβ hρβ ρ htraj
    obtain ⟨h1, -⟩ := hcls ρβ hρβ ρ htraj
    obtain ⟨hp, hb, -, -, hl⟩ := h1 0 le_rfl
    exact ⟨hp, hb, hl⟩
  by_cases hex : ∃ ρβ, IsThermalEquilibrium d 0 a β ρβ
  swap
  · exact ⟨M, L, 1, 1, one_pos, one_pos, fun ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hex⟩
  obtain ⟨ρ₀, hρ₀⟩ := hex
  obtain ⟨-, hpos, Cg, c, hc, hCg⟩ := HRS.MS.MovEnt.s66_rho0_facts hd (s := 0) le_rfl hsd ha hβ hρ₀
  refine ⟨M, L, max Cg 1 * max C₁ 1, c, by positivity, hc, fun ρβ hρβ ρ htraj => ?_⟩
  refine ⟨hround ρβ hρβ ρ htraj, hc, fun x => ?_⟩
  have heq : ρβ = ρ₀ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd le_rfl hsd ha hβ hρβ, HRS.MS.Mov0.mv0_rho_eq hd le_rfl hsd ha hβ hρ₀]
  subst heq
  have hE : 0 < Real.exp (-c * ‖x‖ ^ 2) := Real.exp_pos _
  have hG : ρβ x ≤ max Cg 1 * Real.exp (-c * ‖x‖ ^ 2) :=
    (hCg x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le)
  have hρx := hpos x
  rcases htraj with h | ⟨ε, ψ, -, hres⟩
  · subst h
    have : (1 : ℝ) ≤ max C₁ 1 := le_max_right _ _
    have hpos' : 0 ≤ max Cg 1 * Real.exp (-c * ‖x‖ ^ 2) := by positivity
    show ρβ x ≤ _
    nlinarith
  · have hr := (hres.ratio 0 le_rfl x).2
    have h1 : C₁ * ρβ x ≤ max C₁ 1 * ρβ x := mul_le_mul_of_nonneg_right (le_max_left _ _) hρx.le
    have h2 : max C₁ 1 * ρβ x ≤ max C₁ 1 * (max Cg 1 * Real.exp (-c * ‖x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    calc ρ 0 x ≤ C₁ * ρβ x := hr
      _ ≤ _ := h1.trans h2
      _ = _ := by ring

end HRS.MS.S116

end
