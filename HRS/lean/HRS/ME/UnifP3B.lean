import HRS.ME.UnifP3A

/-!
# Uniform product-moment transfer, part B (packet P3)

`product_moment_transfer_unif`: the uniform form of `HRS.product_moment_transfer_real`
(Lemma 4.4, `M:R:lem:product-transfer`).  All constants (`q`, `C`) are chosen after
`d, s, βm, βp, c₀, Λ, c, ε` and before `β ∈ [βm, βp]` and the density `ρ`, which ranges over smooth
probability densities with `c₀ ≤ ρ ≤ Λ`.  The proof is that of `product_moment_transfer_real`, with
`pressure_all` and `pole_le_gibbs` replaced by `pressure_all_unif` and `pole_le_gibbs_unif`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

theorem product_moment_transfer_unif {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) (c₀ Λ : ℝ) (hc₀ : 0 < c₀)
    (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp,
      ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, c₀ ≤ ρ x) → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N →
      (∀ Y : Config d N → ℝ, Measurable Y →
        eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => withDensityReal ρ)) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ Y : Config d (N - 1) → ℝ, Measurable Y →
        eLpNorm Y 2 (critPole d s c β ρ N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞)
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
  intro ε hε
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨C, hCnn, hC⟩ := pressure_all_unif hd hs0 hsd βm βp hβm hβ c₀ hc₀ Λ
  obtain ⟨D, hD0, hD⟩ := pole_le_gibbs_unif hd hs0 hsd βm βp hβm hβ Λ c hc
  obtain ⟨q, hq2, hqe⟩ : ∃ q : ℕ, 2 ≤ q ∧ 3 * C / (2 * (q : ℝ)) ≤ ε := by
    refine ⟨max 2 ⌈3 * C / (2 * ε)⌉₊, le_max_left _ _, ?_⟩
    have hqpos : (0 : ℝ) < ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : 3 * C / (2 * ε) ≤ ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hexp : ((2 * q : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * (q : ℝ)) := by
    rw [show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine ⟨q, hq2, Real.exp ε * (1 + D), fun β hβb ρ hρ hlow hup N hN => ⟨?_, ?_⟩⟩
  · intro Y hY
    have hβ0 : 0 < β := lt_of_lt_of_le hβm hβb.1
    have hCβ : ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc (β / 2) (2 * β),
        ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
          Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
      fun N hN b hb => hC ρ hρ hlow hup N hN b
        ⟨by linarith [hb.1, hβb.1], by linarith [hb.2, hβb.2]⟩
    rw [hexp]
    have hb : β ∈ Set.Icc (β / 2) β := ⟨by linarith, le_rfl⟩
    refine (eLp_gibbs_le hd hs0 hsd β hβ0 hρ hCβ N (by omega) β hb (q : ℝ) hq2R Y hY).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e : C * N * deltaN d s N = C * (1 + Real.log N) := by
      rw [mul_assoc, N_mul_deltaN_crit hcrit (by omega)]
    rw [e]
    refine (growth_bound hCnn hε hq0 hqe (le_refl _ |>.trans' (by omega) : 1 ≤ N) le_rfl).trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith [Real.exp_pos ε]) (by positivity)
  · intro x t ht Y hY
    have hβ0 : 0 < β := lt_of_lt_of_le hβm hβb.1
    have hCβ : ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc (β / 2) (2 * β),
        ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
          Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
      fun N hN b hb => hC ρ hρ hlow hup N hN b
        ⟨by linarith [hb.1, hβb.1], by linarith [hb.2, hβb.2]⟩
    rw [hexp]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : 1 ≤ N - 1 := by omega
    have hb : ((N - 1 : ℕ) : ℝ) * β / N ∈ Set.Icc (β / 2) β := by
      have h1 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      constructor
      · rw [h1, le_div_iff₀ hN0]; nlinarith
      · rw [h1, div_le_iff₀ hN0]; nlinarith
    have hpole := eLpNorm_mono_measure Y (p := 2) (hD β hβb ρ hρ hup N hN x t ht)
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) Y _ hY.aestronglyMeasurable] at hpole
    have hg := eLp_gibbs_le hd hs0 hsd β hβ0 hρ hCβ (N - 1) hN1 _ hb (q : ℝ) hq2R Y hY
    refine hpole.trans ?_
    have hsq : ENNReal.ofReal D ^ (1 / (2 : ℝ≥0∞)).toReal ≤ ENNReal.ofReal (1 + D) := by
      have : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
      rw [this, ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.sqrt_eq_rpow]
      nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg D]
    have hfac : Real.exp (3 * (C * ((N - 1 : ℕ) : ℝ) * deltaN d s (N - 1)) / (2 * (q : ℝ))) ≤
        Real.exp ε * (N : ℝ) ^ ε := by
      have e : C * ((N - 1 : ℕ) : ℝ) * deltaN d s (N - 1) = C * (1 + Real.log ((N - 1 : ℕ) : ℝ)) := by
        rw [mul_assoc, N_mul_deltaN_crit hcrit hN1]
      rw [e]
      exact growth_bound hCnn hε hq0 hqe hN1 (Nat.sub_le N 1)
    calc ENNReal.ofReal D ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm Y 2
          (modulatedGibbs (periodicRiesz d s) (N - 1) (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ))
        ≤ ENNReal.ofReal (1 + D) * (ENNReal.ofReal (Real.exp ε * (N : ℝ) ^ ε) *
            eLpNorm Y (ENNReal.ofReal (2 * (q : ℝ)))
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
          rw [smul_eq_mul]
          exact mul_le_mul' hsq (hg.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hfac) le_rfl))
      _ = ENNReal.ofReal (Real.exp ε * (1 + D) * (N : ℝ) ^ ε) *
            eLpNorm Y (ENNReal.ofReal (2 * (q : ℝ)))
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring

end HRS.ME.Unif

end
