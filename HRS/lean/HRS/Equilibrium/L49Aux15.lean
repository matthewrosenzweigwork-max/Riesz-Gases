/-
# HRS.Equilibrium.L49Aux15 — Proposition 4.9 (`M:R:prop:insertion-coefficient`): assembly

`insertion_coefficient_proof` (verbatim statement of `HRS.insertion_coefficient`), tied to the
original by `type_of%` at the end of the file.

Chain (TeX lines 4389-4426): `D_N = n ∫ H(λ g) dμ + O(√(log N)/N)` (`l49_time_integral`, with
`l49_AB_bound`), `∫ H(λ g) dμ = (|S|/d) ρ(x) λ² log(1/λ) + O(λ²)` (`l49_compensated`),
`n λ² log(1/λ) = β² δ_N + O(1/N)` (`l49_term3`); finitely many small `N` are absorbed with
`D_N ≤ C δ_N` (`cavity_response_proof`).
-/
import HRS.Equilibrium.L49Aux14

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s : ℝ}

open HRS.ProdTransfer

theorem l49_term3 (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 2 ≤ N) {β Sd ρx Λ : ℝ} (hβ : 0 < β)
    (hSd : 0 ≤ Sd) (hρ0 : 0 ≤ ρx) (hρΛ : ρx ≤ Λ) :
    |((N - 1 : ℕ) : ℝ) * (Sd * ρx * (β / N) ^ 2 * Real.log (1 / (β / N))) -
        β ^ 2 * Sd * ρx * deltaN d s N| ≤ Sd * Λ * β ^ 2 * (2 + |Real.log β|) / N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hNδ : (N : ℝ) * deltaN d s N = 1 + Real.log N := N_mul_deltaN_crit hcrit (by omega)
  have hδ : deltaN d s N = (1 + Real.log N) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNδ
  have hn : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  set ℒ : ℝ := Real.log N with hℒ
  set lb : ℝ := Real.log β with hlb
  have hℒ0 : 0 ≤ ℒ := Real.log_nonneg hN1
  have hℒN : ℒ ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  have hlog : Real.log (1 / (β / N)) = ℒ - lb := by
    rw [one_div, Real.log_inv, Real.log_div hβ.ne' hN0.ne']; ring
  rw [hn, hlog, hδ]
  have e : ((N : ℝ) - 1) * (Sd * ρx * (β / N) ^ 2 * (ℒ - lb)) - β ^ 2 * Sd * ρx * ((1 + ℒ) / N) =
      (Sd * ρx * β ^ 2) * ((-ℒ - ((N : ℝ) - 1) * lb - N) / (N : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Sd * ρx * β ^ 2)]
  have h1 : |(-ℒ - ((N : ℝ) - 1) * lb - N) / (N : ℝ) ^ 2| ≤ (2 + |lb|) / N := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2), div_le_div_iff₀ (by positivity) hN0]
    have h2 : |-ℒ - ((N : ℝ) - 1) * lb - N| ≤ ℒ + ((N : ℝ) - 1) * |lb| + N := by
      calc |-ℒ - ((N : ℝ) - 1) * lb - N| ≤ |-ℒ - ((N : ℝ) - 1) * lb| + |(N : ℝ)| := abs_sub _ _
        _ ≤ (|ℒ| + |((N : ℝ) - 1) * lb|) + |(N : ℝ)| := by
            gcongr
            calc |-ℒ - ((N : ℝ) - 1) * lb| ≤ |-ℒ| + |((N : ℝ) - 1) * lb| := abs_sub _ _
              _ = _ := by rw [abs_neg]
        _ = ℒ + ((N : ℝ) - 1) * |lb| + N := by
            rw [abs_of_nonneg hℒ0, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1),
              abs_of_pos hN0]
    have h3 : ℒ + ((N : ℝ) - 1) * |lb| + N ≤ (2 + |lb|) * N := by
      have := abs_nonneg lb
      nlinarith
    calc |-ℒ - ((N : ℝ) - 1) * lb - N| * N ≤ (ℒ + ((N : ℝ) - 1) * |lb| + N) * N :=
          mul_le_mul_of_nonneg_right h2 hN0.le
      _ ≤ ((2 + |lb|) * N) * N := mul_le_mul_of_nonneg_right h3 hN0.le
      _ = (2 + |lb|) * (N : ℝ) ^ 2 := by ring
  calc Sd * ρx * β ^ 2 * |(-ℒ - ((N : ℝ) - 1) * lb - N) / (N : ℝ) ^ 2|
      ≤ Sd * ρx * β ^ 2 * ((2 + |lb|) / N) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ Sd * Λ * β ^ 2 * ((2 + |lb|) / N) := by
        have : 0 ≤ (2 + |lb|) / N := by positivity
        have h4 : Sd * ρx * β ^ 2 ≤ Sd * Λ * β ^ 2 := by
          have := mul_le_mul_of_nonneg_left hρΛ hSd
          nlinarith [sq_nonneg β]
        exact mul_le_mul_of_nonneg_right h4 this
    _ = _ := by ring

end L49

open HRS.L49 HRS.PoleCavityAux HRS.CavResp HRS.ProdTransfer in
set_option maxHeartbeats 6400000 in
/-- Proposition 4.9 `M:R:prop:insertion-coefficient` (verbatim statement of
`HRS.insertion_coefficient`). -/
theorem insertion_coefficient_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      |insertionDefect d s c β ρ N x - β ^ 2 * sphereArea d / d * ρ x * deltaN d s N| ≤
        C * Real.sqrt (Real.log N) / N := by
  obtain ⟨K₁, K₂, K₃, Cc, lam0, hK1, hK2, hK3, hl0, hl01, hcomp, htime⟩ :=
    l49_time_integral hd hcrit hβ hρ hc
  obtain ⟨KAB, hKAB0, hAB⟩ := l49_AB_bound (d := d) (s := s) hcrit hK1 hK2 hK3
    (b := |Real.log β|) (abs_nonneg _)
  obtain ⟨C0, hcav⟩ := cavity_response_proof hd hcrit β hβ ρ hρ c hc
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  have hSpos : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set Sd : ℝ := sphereArea d / d with hSd
  have hSd0 : 0 ≤ Sd := by positivity
  set ℓ₂ : ℝ := Real.log 2 with hℓ₂
  have hℓ₂0 : 0 < ℓ₂ := l49_log2_pos
  set r₂ : ℝ := Real.sqrt ℓ₂ with hr₂
  have hr₂0 : 0 < r₂ := Real.sqrt_pos.2 hℓ₂0
  set lb : ℝ := |Real.log β| with hlb
  have hlb0 : 0 ≤ lb := abs_nonneg _
  set L₁ : ℝ := |Real.log (β / lam0)| with hL₁
  have hL₁0 : 0 ≤ L₁ := abs_nonneg _
  set Cmain : ℝ := β ^ 2 * KAB + β ^ 2 * |Cc| / r₂ + Sd * Λ * β ^ 2 * (2 + lb) / r₂ with hCmain
  set Cs : ℝ := (|C0| + β ^ 2 * Sd * Λ) * (1 + L₁) / r₂ with hCs
  refine ⟨max Cmain Cs, fun N hN x => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  set ℒ : ℝ := Real.log N with hℒ
  have hℒ2 : ℓ₂ ≤ ℒ := l49_log_ge hN
  have hℒ0 : 0 < ℒ := lt_of_lt_of_le hℓ₂0 hℒ2
  have hrr : r₂ ≤ Real.sqrt ℒ := Real.sqrt_le_sqrt hℒ2
  have hsℒ : 0 < Real.sqrt ℒ := Real.sqrt_pos.2 hℒ0
  have hNδ : (N : ℝ) * deltaN d s N = 1 + ℒ := N_mul_deltaN_crit hcrit (by omega)
  have hδ : deltaN d s N = (1 + ℒ) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNδ
  have hδ0 : 0 ≤ deltaN d s N := by rw [hδ]; positivity
  have hρx0 : 0 ≤ ρ x := hρ.density.nonneg x
  have hρxΛ : ρ x ≤ Λ := hΛ x
  have hn : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hn0 : 0 ≤ (N : ℝ) - 1 := by linarith
  set D : ℝ := insertionDefect d s c β ρ N x with hD
  set Mt : ℝ := β ^ 2 * sphereArea d / d * ρ x * deltaN d s N with hMt
  have hMt0 : 0 ≤ Mt := by positivity
  have hMtΛ : Mt ≤ β ^ 2 * Sd * Λ * deltaN d s N := by
    have e : β ^ 2 * sphereArea d / d * ρ x * deltaN d s N = β ^ 2 * Sd * ρ x * deltaN d s N := by
      rw [hSd]; ring
    rw [hMt, e]
    have : β ^ 2 * Sd * ρ x ≤ β ^ 2 * Sd * Λ := mul_le_mul_of_nonneg_left hρxΛ (by positivity)
    exact mul_le_mul_of_nonneg_right this hδ0
  by_cases hmain : β / N ≤ lam0
  · -- the main regime
    have hlam0' : 0 < β / N := by positivity
    have h1 := htime N hN hmain x
    have h1' : |D - ((N - 1 : ℕ) : ℝ) * ∫ y, taylorH ((β / N) * gPlus d s c (x - y))
        ∂(withDensityReal ρ)| ≤ ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (KAB * Real.sqrt ℒ) := by
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact hAB N hN β hβ le_rfl
    set I : ℝ := ∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hI
    have h2 := (hcomp (β / N) hlam0' hmain x).2
    have h2' : |((N - 1 : ℕ) : ℝ) * I - ((N - 1 : ℕ) : ℝ) * (Sd * ρ x * (β / N) ^ 2 *
        Real.log (1 / (β / N)))| ≤ ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity)
    have h3 := l49_term3 hcrit hN hβ hSd0 hρx0 hρxΛ
    have e3 : β ^ 2 * Sd * ρ x * deltaN d s N = Mt := by
      rw [hMt, hSd]; ring
    rw [e3] at h3
    -- combine
    have hsum : |D - Mt| ≤ ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (KAB * Real.sqrt ℒ) +
        ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) + Sd * Λ * β ^ 2 * (2 + lb) / N := by
      calc |D - Mt| = |(D - ((N - 1 : ℕ) : ℝ) * I) + (((N - 1 : ℕ) : ℝ) * I -
              ((N - 1 : ℕ) : ℝ) * (Sd * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N)))) +
            (((N - 1 : ℕ) : ℝ) * (Sd * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N))) - Mt)| := by
            congr 1; ring
        _ ≤ |D - ((N - 1 : ℕ) : ℝ) * I| + |((N - 1 : ℕ) : ℝ) * I -
              ((N - 1 : ℕ) : ℝ) * (Sd * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N)))| +
            |((N - 1 : ℕ) : ℝ) * (Sd * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N))) - Mt| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by linarith
    -- `n λ² ≤ β² / N`
    have hnl : ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 ≤ β ^ 2 / N := by
      rw [hn]
      have e : ((N : ℝ) - 1) * (β / N) ^ 2 = β ^ 2 / N * (((N : ℝ) - 1) / N) := by
        field_simp
      rw [e]
      have : ((N : ℝ) - 1) / N ≤ 1 := (div_le_one hN0).2 (by linarith)
      calc β ^ 2 / N * (((N : ℝ) - 1) / N) ≤ β ^ 2 / N * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hA : ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (KAB * Real.sqrt ℒ) ≤ β ^ 2 * KAB * Real.sqrt ℒ / N := by
      have := mul_le_mul_of_nonneg_right hnl (mul_nonneg hKAB0 hsℒ.le)
      calc _ ≤ β ^ 2 / N * (KAB * Real.sqrt ℒ) := this
        _ = _ := by ring
    have hB : ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) ≤ β ^ 2 * |Cc| / N := by
      have := mul_le_mul_of_nonneg_right hnl (abs_nonneg Cc)
      calc ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) = ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * |Cc| := by ring
        _ ≤ β ^ 2 / N * |Cc| := this
        _ = _ := by ring
    have hX : ∀ X : ℝ, 0 ≤ X → X / N ≤ X / r₂ * Real.sqrt ℒ / N := by
      intro X hX0
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₂0]
      exact mul_le_mul_of_nonneg_left hrr hX0
    have hsq := hX (β ^ 2 * |Cc|) (by positivity)
    have hC3 := hX (Sd * Λ * β ^ 2 * (2 + lb)) (by positivity)
    have hCm : Cmain * Real.sqrt ℒ / N ≤ max Cmain Cs * Real.sqrt ℒ / N := by
      gcongr
      exact le_max_left _ _
    calc |D - Mt| ≤ _ := hsum
      _ ≤ β ^ 2 * KAB * Real.sqrt ℒ / N + β ^ 2 * |Cc| / N + Sd * Λ * β ^ 2 * (2 + lb) / N := by
          linarith
      _ ≤ β ^ 2 * KAB * Real.sqrt ℒ / N + β ^ 2 * |Cc| / r₂ * Real.sqrt ℒ / N +
            Sd * Λ * β ^ 2 * (2 + lb) / r₂ * Real.sqrt ℒ / N := by linarith
      _ = Cmain * Real.sqrt ℒ / N := by rw [hCmain]; ring
      _ ≤ _ := hCm
  · -- the finitely many small `N`
    push Not at hmain
    have hNle : (N : ℝ) < β / lam0 := by
      have h1 := (lt_div_iff₀ hN0).1 hmain
      exact (lt_div_iff₀ hl0).2 (by linarith)
    obtain ⟨-, -, hD0, -, hDle⟩ := (hcav N hN).1 x
    have hDle' : D ≤ |C0| * deltaN d s N :=
      hDle.trans (mul_le_mul_of_nonneg_right (le_abs_self C0) hδ0)
    have hD0' : 0 ≤ D := hD0
    have habs : |D - Mt| ≤ D + Mt := by
      rw [abs_le]; constructor <;> linarith
    have hsmall : |D - Mt| ≤ (|C0| + β ^ 2 * Sd * Λ) * deltaN d s N := by
      have := habs
      nlinarith [hDle', hMtΛ]
    have hℒle : ℒ ≤ L₁ := by
      have hlogN : ℒ ≤ Real.log (β / lam0) := Real.log_le_log hN0 hNle.le
      exact hlogN.trans (le_abs_self _)
    have hδle : deltaN d s N ≤ (1 + L₁) / r₂ * Real.sqrt ℒ / N := by
      rw [hδ]
      rw [div_mul_eq_mul_div, div_div]
      rw [div_le_div_iff₀ hN0 (by positivity)]
      have h1 : 1 + ℒ ≤ 1 + L₁ := by linarith
      have h2 : (1 + L₁) * r₂ ≤ (1 + L₁) * Real.sqrt ℒ := mul_le_mul_of_nonneg_left hrr (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h1 hr₂0.le]
    calc |D - Mt| ≤ (|C0| + β ^ 2 * Sd * Λ) * deltaN d s N := hsmall
      _ ≤ (|C0| + β ^ 2 * Sd * Λ) * ((1 + L₁) / r₂ * Real.sqrt ℒ / N) :=
          mul_le_mul_of_nonneg_left hδle (by positivity)
      _ = Cs * Real.sqrt ℒ / N := by rw [hCs]; ring
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

example := (@insertion_coefficient_proof : type_of% @HRS.insertion_coefficient)

end HRS

end
