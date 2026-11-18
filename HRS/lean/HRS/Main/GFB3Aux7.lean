import HRS.Main.GFB3Aux6
import HRS.Uniform.Q14Aux6
import HRS.Uniform.Q54cAux58

/-!
# Packet GFB3, part 7: the particle martingale (`gf_particle_martingale`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform

variable {d : ℕ}

lemma gfb3_noise_scale_sq (S : GeneralSetup d) (N : ℕ) (hN : 1 ≤ N) :
    (noiseScale S N / N) ^ 2 = 2 * qN S N / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold noiseScale qN sigN qScale
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hinv : 0 ≤ S.invβ N := S.hinvβ N
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp

lemma gfb3_hsCov_eq_covForm (S : GeneralSetup d) (N : ℕ) (hN : 1 ≤ N) (x : Config d N) :
    hsCovForm (fun k : Fin N × Fin d => (noiseScale S N / N) • bVec (S.γ : ℝ) k.2 (x k.1)) =
      covForm (S.γ : ℝ) (qN S N) (empirical x) := by
  have hγ2 : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h := S.hγ
    have : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h
    push_cast at this
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hq : 0 ≤ qN S N := (Q54c.qScale_bounds (by omega) (S.hκ N) (S.hinvβ N)).1
  haveI : IsProbabilityMeasure (empirical x) := empirical_isProbabilityMeasure (by omega) x
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable fun k : Fin N × Fin d =>
      ‖(noiseScale S N / N) • bVec (S.γ : ℝ) k.2 (x k.1)‖ ^ 2 := Summable.of_finite
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
  have h1 := gfb3_noise_scale_sq S N hN
  have h2 : Real.sqrt (2 * qN S N) * Real.sqrt (2 * qN S N) = 2 * qN S N :=
    Real.mul_self_sqrt (by positivity)
  have h3 : (noiseScale S N / N) * (noiseScale S N / N) = 2 * qN S N / N := by rw [← sq]; exact h1
  calc (noiseScale S N / N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) a *
        ((noiseScale S N / N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) b)
      = ((noiseScale S N / N) * (noiseScale S N / N)) *
        (inner ℝ (bVec (S.γ : ℝ) j (x i)) a * inner ℝ (bVec (S.γ : ℝ) j (x i)) b) := by ring
    _ = (N : ℝ)⁻¹ * ((Real.sqrt (2 * qN S N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) a) *
        (Real.sqrt (2 * qN S N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) b)) := by
        rw [h3]
        have : (Real.sqrt (2 * qN S N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) a) *
            (Real.sqrt (2 * qN S N) * inner ℝ (bVec (S.γ : ℝ) j (x i)) b) =
            (Real.sqrt (2 * qN S N) * Real.sqrt (2 * qN S N)) *
            (inner ℝ (bVec (S.γ : ℝ) j (x i)) a * inner ℝ (bVec (S.γ : ℝ) j (x i)) b) := by ring
        rw [this, h2]
        field_simp

lemma gfb3_noise_norm_le (S : GeneralSetup d) (N : ℕ) (k : Fin N × Fin d) (a : Torus d) :
    ‖(noiseScale S N / N) • bVec (S.γ : ℝ) k.2 a‖ ≤
      |noiseScale S N / N| * Real.sqrt (2 * Q14.q14S d ((S.γ : ℝ) - 1)) := by
  have hγ2 : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h := S.hγ
    have : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h
    push_cast at this
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖bVec (S.γ : ℝ) k.2 a‖ = Real.sqrt (‖bVec (S.γ : ℝ) k.2 a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Q14.q14_norm_bVec_sq_le hγ2 k.2 a)

lemma gfb3_noise_isHS (S : GeneralSetup d) (N : ℕ) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (hF : IsFilteredSolution P ℱ W' W X)
    (T : ℝ) :
    IsHSIntegrand P ℱ T
      (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) := by
  have hγ2 : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h := S.hγ
    have : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h
    push_cast at this
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨?_, fun r ω => Summable.of_finite, ?_⟩
  · intro k i
    have hg : Measurable fun x : Config d N => (noiseScale S N / N) • bVec (S.γ : ℝ) k.2 (x k.1) :=
      (((Q14.q14_continuous_bVec hγ2 k.2).measurable.const_smul (noiseScale S N / N)).comp
        (measurable_pi_apply k.1) : Measurable fun x : Config d N =>
          ((noiseScale S N / N) • bVec (S.γ : ℝ) k.2) (x k.1))
    exact hg.comp (hF.progressive i)
  · set B : ℝ := |noiseScale S N / N| * Real.sqrt (2 * Q14.q14S d ((S.γ : ℝ) - 1)) with hB
    have hpt : ∀ r ω, ∑' k : Fin N × Fin d,
        ‖noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r)) r ω k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r ω
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖noiseIntegrand (S.γ : ℝ) (noiseScale S N)
            (fun r => X (Real.toNNReal r)) r ω k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (gfb3_noise_norm_le S N k _)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r => hpt r ω) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

/-- **GF-PM**, relocated proof. -/
theorem gf_particle_martingale_proof (S : GeneralSetup d) (N : ℕ) (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ),
      IsHilbertItoIntegral P ℱ W'
        (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) Mart ∧
      IsHilbertMartingaleWithCovariation P ℱ S.T Mart
        (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω))) := by
  have hW : IsCylindricalBrownian P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ := gfb3_noise_isHS S N P ℱ W' W X hF
  obtain ⟨Mart, hc, had, hz, hJ⟩ := gfb3_exists_hilbert_version hW hZ
  refine ⟨Mart, ⟨hc, had, hz, ?_⟩, ?_⟩
  · intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  · have hM := HRS.Uniform.Q07c.isHM_of_ito hW (fun T => gfb3_noise_isHS S N P ℱ W' W X hF T) hc had hz hJ S.T
    have hfun : (fun r ω => hsCovForm
        (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r)) r ω)) =
        fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) := by
      funext r ω
      exact gfb3_hsCov_eq_covForm S N hN _
    rw [hfun] at hM
    exact hM

example := (@gf_particle_martingale_proof : type_of% @HRS.GF.gf_particle_martingale)

end HRS.GF
