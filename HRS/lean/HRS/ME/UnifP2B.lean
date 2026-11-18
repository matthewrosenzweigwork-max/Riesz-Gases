import HRS.ME.NfUPU1aA
import HRS.Main.EqMargU1

/-!
# Uniform Lemma 4.1 (`M:A:lem:pole`), packet P2

Constants chosen before `β ∈ [βm, βp]` and before the density `ρ` (smooth positive probability density with
`ρ ≤ Λ`; the lower bound `c₀ ≤ ρ` is not needed):

* `pole_density_clauses_unif`: the one- and two-particle density clauses of `PoleCavityAux.pole_density_clauses`
  (the kernel data `B, Cc` come from `NfU.kerData_periodicRiesz_unif`, `Kbound` is monotone in `β`).
* `pole_variance_clause_unif`: the variance clause, i.e. `HRS.EqMarg.eqmarg_pole_variance` (EqMargU1), whose
  quantitative smallness threshold `n₀` of the calibration field is chosen at `β = βp` with the split
  parameters of `eqmarg_split_params`; restated here with `β ∈ Set.Icc βm βp`.
* `pole_variance_density_unif`: all three clauses of Lemma 4.1 together.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.PoleCavityAux

variable {d : ℕ} {s : ℝ}

/-- `Kbound g B Cc β k` is nondecreasing in `β` (for `B, Cc, k ≥ 0`). -/
theorem Kbound_mono_k {g : Torus d → ℝ} {B Cc β β' k : ℝ} (hB : 0 ≤ B) (hCc : 0 ≤ Cc) (hk : 0 ≤ k)
    (h : β ≤ β') : Kbound g B Cc β k ≤ Kbound g B Cc β' k := by
  have h0 := abs_nonneg (g 0)
  have e : ∀ b : ℝ, Kbound g B Cc b k = b * (k * Cc + (1 / 2) * (B * k ^ 2 + k * |g 0|) + B * k +
      k * (2 * Cc) + (1 / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) + k * Cc) := by
    intro b; unfold Kbound; ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- Uniform `pole_density_clauses`: the constant `C` is chosen before `β ∈ [βm, βp]` and before `ρ`. -/
theorem pole_density_clauses_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
              (withDensityReal ρ) y ≤
            ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))) ∧
      (∀ i j : Fin (N - 1), i ≠ j →
        twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j ≪
            (withDensityReal ρ).prod (withDensityReal ρ) ∧
          ∀ᵐ p ∂((withDensityReal ρ).prod (withDensityReal ρ)),
            (twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
                i j).rnDeriv ((withDensityReal ρ).prod (withDensityReal ρ)) p ≤
              ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
                (periodicRiesz d s (x - p.1) + periodicRiesz d s (x - p.2))))) := by
  obtain ⟨B, Cc, hB, hKU⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  refine ⟨max (Real.exp (Kbound (periodicRiesz d s) B Cc βp 1))
    (Real.exp (Kbound (periodicRiesz d s) B Cc βp 2)), lt_max_of_lt_left (Real.exp_pos _), ?_⟩
  intro β hβb ρ hρ hΛ N hN x t ht
  have hβ : 0 < β := lt_of_lt_of_le hβm hβb.1
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 ≤ β / N := by positivity
  have hlb : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]
    linarith
  have := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t ht).2
  have hn : 0 < N - 1 := by omega
  have hKm := hK.Cc_nonneg
  have hC1 : Real.exp (Kbound (periodicRiesz d s) B Cc β 1) ≤
      max (Real.exp (Kbound (periodicRiesz d s) B Cc βp 1))
        (Real.exp (Kbound (periodicRiesz d s) B Cc βp 2)) :=
    (Real.exp_le_exp.2 (Kbound_mono_k hB hKm (by norm_num) hβb.2)).trans (le_max_left _ _)
  have hC2 : Real.exp (Kbound (periodicRiesz d s) B Cc β 2) ≤
      max (Real.exp (Kbound (periodicRiesz d s) B Cc βp 1))
        (Real.exp (Kbound (periodicRiesz d s) B Cc βp 2)) :=
    (Real.exp_le_exp.2 (Kbound_mono_k hB hKm (by norm_num) hβb.2)).trans (le_max_right _ _)
  constructor
  · have h1 := pole_one_le hK hB (⟨0, hn⟩ : Fin (N - 1)) hβ.le ht.1 ht.2 hl hlb hln x
      (hP := ‹_›)
    have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn⟩) := by
      unfold firstMarginal
      rw [dif_pos hn]
    rw [hfm]
    have : IsProbabilityMeasure ((poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn⟩)) :=
      inferInstance
    obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity _ _ _ h1
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le)
  · intro i j hij
    have h2 := pole_two_le hK hB i j hij hβ.le ht.1 ht.2 hl hlb hln x (hP := ‹_›)
    have : IsProbabilityMeasure (twoMarginal
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j) :=
      by unfold twoMarginal; infer_instance
    obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity _ _ _ h2
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

/-- Uniform variance clause of Lemma 4.1 (`A:eq:pole-variance`): `C` depends only on `[βm, βp]` and `Λ`
(this is `EqMarg.eqmarg_pole_variance`, stated with `β ∈ Set.Icc βm βp`). -/
theorem pole_variance_clause_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := EqMarg.eqmarg_pole_variance hd hs0 hsd βm βp hβm Λ
  exact ⟨C, hC0, fun β hβ ρ hρ hΛ => hC β hβ.1 hβ.2 ρ hρ hΛ⟩

/-- **Lemma 4.1 (`M:A:lem:pole`), uniform form**: variance, one- and two-particle density clauses, with
`C` chosen before `β ∈ [βm, βp]` and before `ρ` (smooth positive probability density, `ρ ≤ Λ`). -/
theorem pole_variance_density_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ)) ∧
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
              (withDensityReal ρ) y ≤
            ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))) ∧
      (∀ i j : Fin (N - 1), i ≠ j →
        twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j ≪
            (withDensityReal ρ).prod (withDensityReal ρ) ∧
          ∀ᵐ p ∂((withDensityReal ρ).prod (withDensityReal ρ)),
            (twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
                i j).rnDeriv ((withDensityReal ρ).prod (withDensityReal ρ)) p ≤
              ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
                (periodicRiesz d s (x - p.1) + periodicRiesz d s (x - p.2))))) := by
  obtain ⟨C1, hC1, h1⟩ := pole_density_clauses_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨C2, hC2, h2⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun β hβ ρ hρ hΛ N hN x t ht => ⟨?_, ?_, ?_⟩⟩
  · intro f hf
    refine (h2 β hβ ρ hρ hΛ N hN x t ht f hf).trans ?_
    gcongr
    exact le_max_right _ _
  · obtain ⟨hac, hle⟩ := (h1 β hβ ρ hρ hΛ N hN x t ht).1
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    gcongr
    exact le_max_left _ _
  · intro i j hij
    obtain ⟨hac, hle⟩ := (h1 β hβ ρ hρ hΛ N hN x t ht).2 i j hij
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    gcongr
    exact le_max_left _ _

end HRS.ME.Unif

end
