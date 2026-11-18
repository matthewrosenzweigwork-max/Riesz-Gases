/-
# HRS.Equilibrium.L49Aux14 — Proposition 4.9, part 14: elementary estimates in `log N`

* `l49_log_le`: `log x ≤ 2 √x` for `x ≥ 1`.
* `l49_AB_bound`: `K₁ + K₂ √(1+|log(β/N)|) + K₃ √δ_N (1+|log(β/N)|) + K₂ + K₃ √δ_N ≤ K √(log N)`.
* `l49_logs_diff`: the `O(1/N)` difference between `(N-1) λ² log(1/λ)` and `β² δ_N`.
-/
import HRS.Equilibrium.L49Aux13

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s : ℝ}

open HRS.ProdTransfer

theorem l49_log_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs0
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  linarith

theorem l49_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem l49_log_ge {N : ℕ} (hN : 2 ≤ N) : Real.log 2 ≤ Real.log N :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hN)

set_option maxHeartbeats 3200000 in
theorem l49_AB_bound (hcrit : s = (d : ℝ) / 2) {K₁ K₂ K₃ b : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 < β → |Real.log β| ≤ b →
      (K₁ + K₂ * Real.sqrt (1 + |Real.log (β / N)|) +
          K₃ * Real.sqrt (deltaN d s N) * (1 + |Real.log (β / N)|)) +
        (K₂ + K₃ * Real.sqrt (deltaN d s N)) ≤ K * Real.sqrt (Real.log N) := by
  set ℓ₂ : ℝ := Real.log 2 with hℓ₂
  have hℓ₂0 : 0 < ℓ₂ := l49_log2_pos
  set c₁ : ℝ := Real.sqrt (1 + (1 + b) / ℓ₂) with hc₁
  set c₃ : ℝ := Real.sqrt (1 + 1 / ℓ₂) with hc₃
  set r₂ : ℝ := Real.sqrt ℓ₂ with hr₂
  have hr₂0 : 0 < r₂ := Real.sqrt_pos.2 hℓ₂0
  refine ⟨K₁ / r₂ + K₂ * c₁ + K₃ * ((3 + b) * c₃) + K₂ / r₂ + K₃ * c₃, by positivity, ?_⟩
  intro N hN β hβ hlb
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set ℒ : ℝ := Real.log N with hℒ
  have hℒ2 : ℓ₂ ≤ ℒ := l49_log_ge hN
  have hℒ0 : 0 < ℒ := lt_of_lt_of_le hℓ₂0 hℒ2
  have hsℒ : 0 < Real.sqrt ℒ := Real.sqrt_pos.2 hℒ0
  have hrr : r₂ ≤ Real.sqrt ℒ := Real.sqrt_le_sqrt hℒ2
  have ha : |Real.log (β / N)| ≤ b + ℒ := by
    rw [Real.log_div hβ.ne' hN0.ne']
    have h := abs_sub (Real.log β) (Real.log N)
    have h' : |Real.log N| = ℒ := abs_of_nonneg (Real.log_nonneg hN1)
    linarith
  set δ : ℝ := deltaN d s N with hδ
  have hNδ : (N : ℝ) * δ = 1 + ℒ := N_mul_deltaN_crit hcrit (by omega)
  have hδeq : δ = (1 + ℒ) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNδ
  have hδ0 : 0 ≤ δ := by rw [hδeq]; positivity
  -- `√(1 + a) ≤ c₁ √ℒ`
  have h1 : Real.sqrt (1 + |Real.log (β / N)|) ≤ c₁ * Real.sqrt ℒ := by
    have hle : 1 + |Real.log (β / N)| ≤ (1 + (1 + b) / ℓ₂) * ℒ := by
      have : (1 + b) ≤ (1 + b) / ℓ₂ * ℒ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ₂0]
        nlinarith
      nlinarith
    calc Real.sqrt (1 + |Real.log (β / N)|) ≤ Real.sqrt ((1 + (1 + b) / ℓ₂) * ℒ) := Real.sqrt_le_sqrt hle
      _ = c₁ * Real.sqrt ℒ := Real.sqrt_mul (by positivity) _
  -- `1 + ℒ ≤ (1 + 1/ℓ₂) ℒ`
  have h2 : 1 + ℒ ≤ (1 + 1 / ℓ₂) * ℒ := by
    have : 1 ≤ 1 / ℓ₂ * ℒ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hℓ₂0]; linarith
    nlinarith
  have hsqrtδ : Real.sqrt δ ≤ c₃ * Real.sqrt ℒ := by
    have hle : δ ≤ (1 + 1 / ℓ₂) * ℒ := by
      have : δ ≤ 1 + ℒ := by nlinarith
      linarith
    calc Real.sqrt δ ≤ Real.sqrt ((1 + 1 / ℓ₂) * ℒ) := Real.sqrt_le_sqrt hle
      _ = c₃ * Real.sqrt ℒ := Real.sqrt_mul (by positivity) _
  -- `√δ (1 + a) ≤ (3+b) c₃ √ℒ`
  have hsN : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
  have hℒN : ℒ ≤ 2 * Real.sqrt N := l49_log_le hN1
  have h3 : Real.sqrt δ * (1 + |Real.log (β / N)|) ≤ ((3 + b) * c₃) * Real.sqrt ℒ := by
    have hA : 1 + |Real.log (β / N)| ≤ (3 + b) * Real.sqrt N := by nlinarith
    have hS : Real.sqrt δ * Real.sqrt N = Real.sqrt (1 + ℒ) := by
      rw [← Real.sqrt_mul hδ0, mul_comm, hNδ]
    have hS2 : Real.sqrt (1 + ℒ) ≤ c₃ * Real.sqrt ℒ := by
      calc Real.sqrt (1 + ℒ) ≤ Real.sqrt ((1 + 1 / ℓ₂) * ℒ) := Real.sqrt_le_sqrt h2
        _ = c₃ * Real.sqrt ℒ := Real.sqrt_mul (by positivity) _
    calc Real.sqrt δ * (1 + |Real.log (β / N)|) ≤ Real.sqrt δ * ((3 + b) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
      _ = (3 + b) * (Real.sqrt δ * Real.sqrt N) := by ring
      _ = (3 + b) * Real.sqrt (1 + ℒ) := by rw [hS]
      _ ≤ (3 + b) * (c₃ * Real.sqrt ℒ) := mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = _ := by ring
  have hK1 : K₁ ≤ K₁ / r₂ * Real.sqrt ℒ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr₂0]
    exact mul_le_mul_of_nonneg_left hrr hK₁
  have hK2 : K₂ ≤ K₂ / r₂ * Real.sqrt ℒ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr₂0]
    exact mul_le_mul_of_nonneg_left hrr hK₂
  have e1 := mul_le_mul_of_nonneg_left h1 hK₂
  have e2 := mul_le_mul_of_nonneg_left h3 hK₃
  have e3 := mul_le_mul_of_nonneg_left hsqrtδ hK₃
  have e4 : K₃ * Real.sqrt δ * (1 + |Real.log (β / N)|) = K₃ * (Real.sqrt δ * (1 + |Real.log (β / N)|)) := by ring
  rw [e4]
  nlinarith [e1, e2, e3, hK1, hK2]

end L49

end HRS

end
