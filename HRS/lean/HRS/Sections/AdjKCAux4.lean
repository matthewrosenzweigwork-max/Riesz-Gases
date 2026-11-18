import HRS.Sections.AdjKSpec
import HRS.Main.GFB3Aux13
import HRS.Main.GFB1Aux1

/-!
# ADJKC Aux4: packet B0 (`E_n`-valued particle martingale), helpers

A re-run of the `GF.gf_particle_martingale_proof` chain outside `GeneralSetup`: real index `n > d/2+2`, noise scale
`c₀ = √N √(2q)` with `q = β⁻¹`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjKC

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

lemma adjkc_hsCov_eq_covForm {γ : ℝ} (hγ2 : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q) (N : ℕ)
    (hN : 1 ≤ N) (c0 : ℝ) (hc : (c0 / N) ^ 2 = 2 * q / N) (x : Config d N) :
    hsCovForm (fun k : Fin N × Fin d => (c0 / N) • bVec γ k.2 (x k.1)) =
      covForm γ q (empirical x) := by
  haveI : IsProbabilityMeasure (empirical x) := empirical_isProbabilityMeasure (by omega) x
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable fun k : Fin N × Fin d =>
      ‖(c0 / N) • bVec γ k.2 (x k.1)‖ ^ 2 := Summable.of_finite
  ext a b
  rw [hsCovForm_apply hsum, HRS.Uniform.Q14.q14_covForm_apply hγ2 hq]
  rw [tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hint : ∀ g : Torus d → ℝ, ∫ u, g u ∂(empirical x) = (N : ℝ)⁻¹ * ∑ i, g (x i) := fun g =>
    pair_empirical (by omega) x g
  rw [hint]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, conj_trivial]
  have h2 : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q :=
    Real.mul_self_sqrt (by positivity)
  have h3 : (c0 / N) * (c0 / N) = 2 * q / N := by rw [← sq]; exact hc
  calc (c0 / N) * inner ℝ (bVec γ j (x i)) a * ((c0 / N) * inner ℝ (bVec γ j (x i)) b)
      = ((c0 / N) * (c0 / N)) * (inner ℝ (bVec γ j (x i)) a * inner ℝ (bVec γ j (x i)) b) := by ring
    _ = (N : ℝ)⁻¹ * ((Real.sqrt (2 * q) * inner ℝ (bVec γ j (x i)) a) *
        (Real.sqrt (2 * q) * inner ℝ (bVec γ j (x i)) b)) := by
        rw [h3]
        have : (Real.sqrt (2 * q) * inner ℝ (bVec γ j (x i)) a) *
            (Real.sqrt (2 * q) * inner ℝ (bVec γ j (x i)) b) =
            (Real.sqrt (2 * q) * Real.sqrt (2 * q)) *
            (inner ℝ (bVec γ j (x i)) a * inner ℝ (bVec γ j (x i)) b) := by ring
        rw [this, h2]
        field_simp

lemma adjkc_noise_norm_le {γ : ℝ} (hγ2 : (d : ℝ) / 2 + 2 < γ) (N : ℕ) (c0 : ℝ) (k : Fin N × Fin d)
    (a : Torus d) :
    ‖(c0 / N) • bVec γ k.2 a‖ ≤ |c0 / N| * Real.sqrt (2 * Q14.q14S d (γ - 1)) := by
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖bVec γ k.2 a‖ = Real.sqrt (‖bVec γ k.2 a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Q14.q14_norm_bVec_sq_le hγ2 k.2 a)

lemma adjkc_noise_isHS {γ : ℝ} (hγ2 : (d : ℝ) / 2 + 2 < γ) (N : ℕ) (c0 : ℝ) {Ω : Type}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hF : IsFilteredSolution P ℱ W' W X) (T : ℝ) :
    IsHSIntegrand P ℱ T (noiseIntegrand γ c0 (fun r => X (Real.toNNReal r))) := by
  refine ⟨?_, fun r ω => Summable.of_finite, ?_⟩
  · intro k i
    have hg : Measurable fun x : Config d N => (c0 / N) • bVec γ k.2 (x k.1) :=
      (((Q14.q14_continuous_bVec hγ2 k.2).measurable.const_smul (c0 / N)).comp
        (measurable_pi_apply k.1) : Measurable fun x : Config d N =>
          ((c0 / N) • bVec γ k.2) (x k.1))
    exact hg.comp (hF.progressive i)
  · set B : ℝ := |c0 / N| * Real.sqrt (2 * Q14.q14S d (γ - 1)) with hB
    have hpt : ∀ r ω, ∑' k : Fin N × Fin d,
        ‖noiseIntegrand γ c0 (fun r => X (Real.toNNReal r)) r ω k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r ω
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖noiseIntegrand γ c0 (fun r => X (Real.toNNReal r)) r ω k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (adjkc_noise_norm_le hγ2 N c0 k _)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r => hpt r ω) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

end HRS.AdjKC
