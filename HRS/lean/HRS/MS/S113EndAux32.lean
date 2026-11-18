import HRS.MS.S113EndAux31

/-!
# S11.3 endpoint (worker S11X), part 32: X4 (`S113XLogNormalizer`) for `s = 0`, and `r2_moving_Lp` from X2 alone

`s113x_logNormalizer`: for the logarithmic kernel (`s = 0`) the core X4 holds for every tuple of S6.3 constants (the class members have a common Gaussian envelope).
(For `s > 0` the statement is false: `e^{b N F}` is not integrable at coincidences; the core is used only for `γ = 0`, which forces `s = 0`.)
`s113x_r2_moving_Lp_of_X2`: the frozen `r2_moving_Lp` from the single remaining core X2 (`S113XLocalized`) for a tuple `S113XTupleOK`.
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

theorem s113x_logNormalizer (hd : 2 ≤ d) {s : ℝ} (hs : s = 0) {q β : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hC₁ : 0 < C₁)
    (hc₀ : 0 < c₀) (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) :
    S113XLogNormalizer d s q β ρ₀ j m εstar r c₀ := by
  have hsd : s < d := by rw [hs]; exact_mod_cast (by omega : 0 < d)
  obtain ⟨-, -, Cg, cg, hcg, hCg⟩ := HRS.MS.MovEnt.s66_rho0_facts hd (by rw [hs]) hsd hq hβ hρ₀
  obtain ⟨astar, B, hastar, hB0, hall⟩ := s113x_X4_generic (d := d) (by omega) (C₁ * Cg) cg hcg
  refine ⟨astar, hastar, B, fun f0 hf0 ρ hρ' N hN θ hθ => ?_⟩
  obtain ⟨hprob, hpos, hratio, -⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le 0 le_rfl
  have hρ0 : ∀ x, 0 ≤ ρ 0 x ∧ ρ 0 x ≤ C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
    ⟨(hpos x).le, ((hratio x).2).trans (by
      calc C₁ * ρ₀ x ≤ C₁ * (Cg * Real.exp (-cg * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hCg x) hC₁.le
        _ = C₁ * Cg * Real.exp (-cg * ‖x‖ ^ 2) := by ring)⟩
  subst hs
  exact hall (ρ 0) (hρ'.regular 0 le_rfl).measurable hρ0 hprob.integral_one N hN θ hθ

theorem s113x_r2_moving_Lp_of_X2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalized d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hOK, hloc⟩ := hcores
  refine s113x_r2_moving_Lp_of_X2_X4 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hOK, hloc, fun hγ0 => ?_⟩
  have hs00 : s = 0 := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact absurd hγ0 (hγs h).ne'
    · exact h.symm
  obtain ⟨hε, hr, hc₀, hc, hC₁, hNL, -⟩ := hOK
  exact s113x_logNormalizer hd hs00 hβ hq hρ hC₁ hc₀ hNL

theorem s113x_r2_moving_moment_transfer_of_X2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalized d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp' hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113x_r2_moving_Lp_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs hcores)

end HRS.MS.S113BD

end
