import HRS.ME.UnifP5G
import HRS.ME.UnifP6K

/-!
# Uniform Proposition 4.9 (packet P7): proof of `insertion_coefficient_unif`

`insertion_coefficient_unif_proof` has the frozen statement of `insertion_coefficient_unif`
(`HRS/ME/UnifP7Spec.lean`, not edited). The proof follows the body of `HRS.insertion_coefficient_proof`
(`HRS/Equilibrium/L49Aux15.lean`) with uniform inputs: `cavity_response_unif` (UnifP5G, projected to
`CavRespUnif` and to the defect bound in helper `p7_cav`) and `l49_defect_unif` (UnifP6K).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48 HRS.L49

variable {d : ℕ} {s : ℝ}

/-- Triangle inequality helper for the three-term splitting. -/
theorem p7_tri3 (D I M Mt : ℝ) : |D - Mt| ≤ |D - I| + |I - M| + |M - Mt| := by
  have e : D - Mt = (D - I) + (I - M) + (M - Mt) := by ring
  rw [e]
  have a1 := abs_add_le ((D - I) + (I - M)) (M - Mt)
  have a2 := abs_add_le (D - I) (I - M)
  linarith

/-- Projection of `cavity_response_unif`: one constant `Cu` for the defect bounds (clause 4 of
`cavity_response_unif`), and `CavRespUnif` (clauses 2 and 4 of its conclusion, with `max Cu 0`). -/
theorem p7_cav (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) :
    ∃ Cu : ℝ, (∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ N : ℕ, 2 ≤ N →
        ∀ x : Torus d, 0 ≤ insertionDefect d s c β ρ N x ∧
          insertionDefect d s c β ρ N x ≤ Cu * deltaN d s N) ∧
      CavRespUnif d s c βm βp c₀ Λ := by
  obtain ⟨Cu, hCu⟩ := cavity_response_unif hd hcrit βm βp hβm hββ Λ c hc
  refine ⟨Cu, fun β hβ ρ hF N hN x => ?_, ?_⟩
  · obtain ⟨hA, -, -, -, -⟩ := hCu β hβ ρ hF.smooth hF.up N hN
    obtain ⟨-, -, h0, -, hle⟩ := hA x
    exact ⟨h0, hle⟩
  · unfold CavRespUnif
    refine ⟨max Cu 0, le_max_right _ _, fun β hβ ρ hF N hN => ?_⟩
    obtain ⟨-, ⟨hB1, hB2, hB3⟩, -, hD, -⟩ := hCu β hβ ρ hF.smooth hF.up N hN
    refine ⟨⟨hB1, hB2, hB3.trans (ENNReal.ofReal_le_ofReal ?_)⟩, fun x t ht => ?_⟩
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (by positivity)
    · obtain ⟨b1, b2⟩ := hD x t ht
      refine ⟨b1, b2.mono fun y hy => hy.trans ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le

set_option maxHeartbeats 1600000 in
/-- **Proposition 4.9, uniform form** (verbatim statement of `insertion_coefficient_unif`). -/
theorem insertion_coefficient_unif_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ x : Torus d,
      |insertionDefect d s c β ρ N x - β ^ 2 * sphereArea d / d * ρ x * deltaN d s N| ≤
        C * Real.sqrt (Real.log N) / N := by
  obtain ⟨Cu, hdef, hCR⟩ := p7_cav hd hcrit c hc βm βp hβm hββ c₀ Λ
  obtain ⟨K, Cc, lam0, hK0, hl0, -, hcomp, hmain⟩ :=
    l49_defect_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hc₀ hΛ hCR
  have hSpos : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hβp0 : 0 < βp := lt_of_lt_of_le hβm hββ
  have hr₂0 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 l49_log2_pos
  set S : ℝ := sphereArea d / d with hS
  have hSd0 : 0 ≤ S := div_nonneg hSpos.le hd0.le
  set lb : ℝ := max |Real.log βm| |Real.log βp| with hlb
  have hlb0 : 0 ≤ lb := (abs_nonneg _).trans (le_max_left _ _)
  have hlog : ∀ β ∈ Set.Icc βm βp, |Real.log β| ≤ lb := by
    intro β hβI
    have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
    rw [abs_le]
    constructor
    · have h1 : Real.log βm ≤ Real.log β := Real.log_le_log hβm hβI.1
      have h2 : -|Real.log βm| ≤ Real.log βm := neg_abs_le _
      have h3 : |Real.log βm| ≤ lb := le_max_left _ _
      linarith
    · have h1 : Real.log β ≤ Real.log βp := Real.log_le_log hβ hβI.2
      have h2 : Real.log βp ≤ |Real.log βp| := le_abs_self _
      have h3 : |Real.log βp| ≤ lb := le_max_right _ _
      linarith
  set Lstar : ℝ := |Real.log (βp / lam0)| with hLstar
  set r₂ : ℝ := Real.sqrt (Real.log 2) with hr₂
  set Cmain : ℝ := βp ^ 2 * K + βp ^ 2 * |Cc| / r₂ + S * Λ * βp ^ 2 * (2 + lb) / r₂ with hCmain
  set Cs : ℝ := (|Cu| + βp ^ 2 * S * Λ) * (1 + Lstar) / r₂ with hCs
  refine ⟨max Cmain Cs, fun β hβI ρ hF N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβp' : β ≤ βp := hβI.2
  have hβ2 : β ^ 2 ≤ βp ^ 2 := by nlinarith
  have hlbβ : |Real.log β| ≤ lb := hlog β hβI
  have hρx0 : 0 ≤ ρ x := hc₀.le.trans (hF.low x)
  have hρxΛ : ρ x ≤ Λ := hF.up x
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hn : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hn0 : 0 ≤ (N : ℝ) - 1 := by linarith
  set ℒ : ℝ := Real.log N with hℒ
  have hℒ2 : Real.log 2 ≤ ℒ := l49_log_ge hN
  have hℒ0 : 0 < ℒ := lt_of_lt_of_le l49_log2_pos hℒ2
  have hrr : r₂ ≤ Real.sqrt ℒ := Real.sqrt_le_sqrt hℒ2
  have hsℒ : 0 < Real.sqrt ℒ := Real.sqrt_pos.2 hℒ0
  have hNδ : (N : ℝ) * deltaN d s N = 1 + ℒ := N_mul_deltaN_crit hcrit (by omega)
  have hδ : deltaN d s N = (1 + ℒ) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNδ
  have hδ0 : 0 ≤ deltaN d s N := by
    rw [hδ]; exact div_nonneg (by linarith) hN0.le
  set D : ℝ := insertionDefect d s c β ρ N x with hD
  set Mt : ℝ := β ^ 2 * sphereArea d / d * ρ x * deltaN d s N with hMt
  have hMt0 : 0 ≤ Mt := by
    rw [hMt]
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg β) hSpos.le) hd0.le) hρx0) hδ0
  have hMtΛ : Mt ≤ βp ^ 2 * S * Λ * deltaN d s N := by
    have e : Mt = (β ^ 2 * S) * ρ x * deltaN d s N := by
      rw [hMt, hS]; ring
    rw [e]
    have h1 : β ^ 2 * S * ρ x ≤ βp ^ 2 * S * Λ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hβ2 hSd0) hρxΛ hρx0 (mul_nonneg (sq_nonneg _) hSd0)
    exact mul_le_mul_of_nonneg_right h1 hδ0
  have hd2 : 0 ≤ D ∧ D ≤ Cu * deltaN d s N := hdef β hβI ρ hF N hN x
  by_cases hreg : β / N ≤ lam0
  · -- the main regime
    have hlam0' : 0 < β / N := div_pos hβ hN0
    have h1 : |D - ((N - 1 : ℕ) : ℝ) * ∫ y, taylorH ((β / N) * gPlus d s c (x - y))
        ∂(withDensityReal ρ)| ≤ ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (K * Real.sqrt ℒ) :=
      hmain β hβI ρ hF N hN hreg x
    have h2 : |(∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ)) -
        S * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N))| ≤ Cc * (β / N) ^ 2 :=
      (hcomp ρ hF (β / N) hlam0' hreg x).2
    set I : ℝ := ∫ y, taylorH ((β / N) * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hI
    have hB : |((N - 1 : ℕ) : ℝ) * I - ((N - 1 : ℕ) : ℝ) * (S * ρ x * (β / N) ^ 2 *
        Real.log (1 / (β / N)))| ≤ ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity)
    have hC : |((N - 1 : ℕ) : ℝ) * (S * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N))) - Mt| ≤
        S * Λ * β ^ 2 * (2 + |Real.log β|) / N := by
      have h3 := l49_term3 hcrit hN hβ hSd0 hρx0 hρxΛ
      have e3 : β ^ 2 * S * ρ x * deltaN d s N = Mt := by
        rw [hMt, hS]; ring
      rw [← e3]
      exact h3
    have hnl : ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 ≤ β ^ 2 / N := by
      rw [hn]
      have e : ((N : ℝ) - 1) * (β / N) ^ 2 = β ^ 2 / N * (((N : ℝ) - 1) / N) := by
        field_simp
      rw [e]
      have : ((N : ℝ) - 1) / N ≤ 1 := (div_le_one hN0).2 (by linarith)
      calc β ^ 2 / N * (((N : ℝ) - 1) / N) ≤ β ^ 2 / N * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hnl' : ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 ≤ βp ^ 2 / N :=
      hnl.trans (div_le_div_of_nonneg_right hβ2 hN0.le)
    have hX : ∀ X : ℝ, 0 ≤ X → X / N ≤ X / r₂ * Real.sqrt ℒ / N := by
      intro X hX0
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₂0]
      exact mul_le_mul_of_nonneg_left hrr hX0
    -- the three terms, each bounded by (constant) * (√ℒ / N)
    have hT1 : ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * (K * Real.sqrt ℒ) ≤
        βp ^ 2 * K * (Real.sqrt ℒ / N) := by
      have h := mul_le_mul_of_nonneg_right hnl' (mul_nonneg hK0 hsℒ.le)
      calc _ ≤ βp ^ 2 / N * (K * Real.sqrt ℒ) := h
        _ = βp ^ 2 * K * (Real.sqrt ℒ / N) := by ring
    have hT2 : ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) ≤
        βp ^ 2 * |Cc| / r₂ * (Real.sqrt ℒ / N) := by
      calc ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2)
          = ((N - 1 : ℕ) : ℝ) * (β / N) ^ 2 * |Cc| := by ring
        _ ≤ β ^ 2 / N * |Cc| := mul_le_mul_of_nonneg_right hnl (abs_nonneg _)
        _ = β ^ 2 * |Cc| / N := by ring
        _ ≤ βp ^ 2 * |Cc| / N :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hβ2 (abs_nonneg _)) hN0.le
        _ ≤ βp ^ 2 * |Cc| / r₂ * Real.sqrt ℒ / N := hX _ (by positivity)
        _ = _ := by ring
    have hT3 : S * Λ * β ^ 2 * (2 + |Real.log β|) / N ≤
        S * Λ * βp ^ 2 * (2 + lb) / r₂ * (Real.sqrt ℒ / N) := by
      have hS' : 0 ≤ S * Λ := mul_nonneg hSd0 hΛ0
      have h2b : β ^ 2 * (2 + |Real.log β|) ≤ βp ^ 2 * (2 + lb) :=
        mul_le_mul hβ2 (by linarith) (by positivity) (sq_nonneg _)
      have h3b : S * Λ * β ^ 2 * (2 + |Real.log β|) ≤ S * Λ * βp ^ 2 * (2 + lb) := by
        calc S * Λ * β ^ 2 * (2 + |Real.log β|) = (S * Λ) * (β ^ 2 * (2 + |Real.log β|)) := by ring
          _ ≤ (S * Λ) * (βp ^ 2 * (2 + lb)) := mul_le_mul_of_nonneg_left h2b hS'
          _ = S * Λ * βp ^ 2 * (2 + lb) := by ring
      have hXnn : 0 ≤ S * Λ * βp ^ 2 * (2 + lb) :=
        mul_nonneg (mul_nonneg (mul_nonneg hSd0 hΛ0) (sq_nonneg _)) (by linarith)
      calc S * Λ * β ^ 2 * (2 + |Real.log β|) / N ≤ S * Λ * βp ^ 2 * (2 + lb) / N :=
            div_le_div_of_nonneg_right h3b hN0.le
        _ ≤ S * Λ * βp ^ 2 * (2 + lb) / r₂ * Real.sqrt ℒ / N := hX _ hXnn
        _ = _ := by ring
    have hQ : Cmain * (Real.sqrt ℒ / N) = βp ^ 2 * K * (Real.sqrt ℒ / N) +
        βp ^ 2 * |Cc| / r₂ * (Real.sqrt ℒ / N) + S * Λ * βp ^ 2 * (2 + lb) / r₂ * (Real.sqrt ℒ / N) := by
      rw [hCmain]; ring
    have htri := p7_tri3 D (((N - 1 : ℕ) : ℝ) * I)
      (((N - 1 : ℕ) : ℝ) * (S * ρ x * (β / N) ^ 2 * Real.log (1 / (β / N)))) Mt
    have hB' : |((N - 1 : ℕ) : ℝ) * I - ((N - 1 : ℕ) : ℝ) * (S * ρ x * (β / N) ^ 2 *
        Real.log (1 / (β / N)))| ≤ ((N - 1 : ℕ) : ℝ) * (|Cc| * (β / N) ^ 2) := hB
    have hsum : |D - Mt| ≤ Cmain * (Real.sqrt ℒ / N) := by
      rw [hQ]
      linarith
    calc |D - Mt| ≤ Cmain * (Real.sqrt ℒ / N) := hsum
      _ = Cmain * Real.sqrt ℒ / N := by ring
      _ ≤ max Cmain Cs * Real.sqrt ℒ / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hsℒ.le) hN0.le
  · -- the finitely many small `N`
    push Not at hreg
    have hNle : (N : ℝ) ≤ βp / lam0 := by
      rw [le_div_iff₀ hl0]
      have := (lt_div_iff₀ hN0).1 hreg
      linarith
    have hℒle : Real.log N ≤ Lstar := by
      have := Real.log_le_log hN0 hNle
      exact this.trans (le_abs_self _)
    have hδle : deltaN d s N ≤ (1 + Lstar) / r₂ * Real.sqrt ℒ / N := by
      rw [hδ]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      have e1 : (1 + Lstar) / r₂ * r₂ = 1 + Lstar := by field_simp
      have h2 : (1 + Lstar) / r₂ * r₂ ≤ (1 + Lstar) / r₂ * Real.sqrt ℒ :=
        mul_le_mul_of_nonneg_left hrr (div_nonneg (by linarith) hr₂0.le)
      linarith
    have hDle : D ≤ |Cu| * deltaN d s N :=
      hd2.2.trans (mul_le_mul_of_nonneg_right (le_abs_self Cu) hδ0)
    have habs : |D - Mt| ≤ D + Mt := by
      rw [abs_le]; constructor <;> linarith [hd2.1]
    have hsmall : |D - Mt| ≤ (|Cu| + βp ^ 2 * S * Λ) * deltaN d s N := by
      have e : (|Cu| + βp ^ 2 * S * Λ) * deltaN d s N =
          |Cu| * deltaN d s N + βp ^ 2 * S * Λ * deltaN d s N := by ring
      linarith
    calc |D - Mt| ≤ (|Cu| + βp ^ 2 * S * Λ) * deltaN d s N := hsmall
      _ ≤ (|Cu| + βp ^ 2 * S * Λ) * ((1 + Lstar) / r₂ * Real.sqrt ℒ / N) :=
          mul_le_mul_of_nonneg_left hδle
            (add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg _) hSd0) hΛ0))
      _ = Cs * Real.sqrt ℒ / N := by rw [hCs]; ring
      _ ≤ max Cmain Cs * Real.sqrt ℒ / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hsℒ.le) hN0.le


end HRS.ME.Unif

end
