import HRS.MS.R2S11Aux12

/-!
# S11.4: the conditional proof of `r2_moving_moment_transfer`

`s11_moving_moment_transfer_of_Lp`: the frozen statement `r2_moving_moment_transfer` follows from
* `h113`: the conclusion of `r2_moving_Lp` (S11.3) for the same parameters (a hypothesis whose type is the frozen
  conclusion, `type_of%`), and
* `hmeas`: the joint measurability of `(t, x) ↦ ρ t x` for the members of the small class (a true fact: `t ↦ v_t` is continuous
  into `Σ^m ↪ C_b`; not yet proved), used only for the time integral of item (5).

Once S11.3 and the lemma `hmeas` are proved, `example := (@r2_moving_moment_transfer_proof : type_of% @r2_moving_moment_transfer)`.
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

theorem s11_moving_moment_transfer_of_Lp (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hmeas : ∀ (j m : ℕ) (εstar r c₀ : ℝ), (d : ℝ) / 2 + j + 6 < m → ∀ (f0 : Euc d → ℝ), MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
        Measurable fun p : ℝ≥0 × Euc d => ρ p.1 p.2)
    (h113 : type_of% (r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs)) :
    type_of% (r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, pinf, K, hpinf, hAD⟩ :=
    s11_item1_of_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs h113
  refine ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, pinf, K, hpinf, hAD, ?_, ?_⟩
  · intro Λ
    exact s11_velocity_uniform_approx hd hs0 hs hq hβ hρ Λ
  · intro B rr hrr
    have h23 := s11_items23 hd hs0 hs hq hβ hρ hC₁ hc₀ hNL hpinf hAD B rr hrr
    exact ⟨h23, s11_item5 (hmeas j m εstar r c₀ hm) h23⟩

end HRS.MS.R2S11
