import HRS.ME.UnifP6J

/-!
# Uniform Proposition 4.9, part K (packet P6): the defect against `n ∫ H(λ g) dμ`, final form

Combines `l49_time_integral_unif` with `l49_AB_bound` (which is already `ρ`-free) with
`b = max |log βm| |log βp|`: the error is bounded by `(N-1) (β/N)² K √(log N)`, with `K` independent of
`β ∈ [βm, βp]` and of `ρ ∈ UFam d c₀ Λ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48 HRS.L49

variable {d : ℕ} {s : ℝ}

/-- Uniform `l49_time_integral` followed by `l49_AB_bound`. -/
theorem l49_defect_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ K Cc lam0 : ℝ, 0 ≤ K ∧ 0 < lam0 ∧ lam0 ≤ 1 ∧
      (∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ x : Torus d,
        Integrable (fun y => taylorH (lam * gPlus d s c (x - y))) (withDensityReal ρ) ∧
        |∫ y, taylorH (lam * gPlus d s c (x - y)) ∂(withDensityReal ρ) -
            sphereArea d / d * ρ x * lam ^ 2 * Real.log (1 / lam)| ≤ Cc * lam ^ 2) ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → β / N ≤ lam0 → ∀ x : Torus d,
        |insertionDefect d s c β ρ N x -
            ((N - 1 : ℕ) : ℝ) * ∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ)| ≤
          ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (K * Real.sqrt (Real.log N)) := by
  obtain ⟨K₁, K₂, K₃, Cc, lam0, hK₁, hK₂, hK₃, hl0, hl01, hcomp, hmain⟩ :=
    l49_time_integral_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hc₀ hΛ hCR
  have hb : 0 ≤ max |Real.log βm| |Real.log βp| := (abs_nonneg _).trans (le_max_left _ _)
  obtain ⟨K, hK0, hK⟩ := l49_AB_bound (d := d) (s := s) hcrit hK₁ hK₂ hK₃ hb
  refine ⟨K, Cc, lam0, hK0, hl0, hl01, hcomp, ?_⟩
  intro β hβI ρ hF N hN hlam x
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hlog : |Real.log β| ≤ max |Real.log βm| |Real.log βp| := by
    rw [abs_le]
    constructor
    · have h1 : Real.log βm ≤ Real.log β := Real.log_le_log hβm hβI.1
      have h2 : -|Real.log βm| ≤ Real.log βm := neg_abs_le _
      have h3 : |Real.log βm| ≤ max |Real.log βm| |Real.log βp| := le_max_left _ _
      linarith
    · have h1 : Real.log β ≤ Real.log βp := Real.log_le_log hβ hβI.2
      have h2 : Real.log βp ≤ |Real.log βp| := le_abs_self _
      have h3 : |Real.log βp| ≤ max |Real.log βm| |Real.log βp| := le_max_right _ _
      linarith
  refine (hmain β hβI ρ hF N hN hlam x).trans ?_
  have hn0 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (hK N hN β hβ hlog) (by positivity)

end HRS.ME.Unif

end
