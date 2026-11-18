import HRS.MS.MainRdFieldAux11

/-!
# S.A.6, packet P7: existence of the particle field and the first-moment bounds

* `sa6_exists_Xi`: a measurable `H^{-Γ}`-valued random variable representing `σ_N(μ_N^t - μ_{β_N}^t)` (Riesz representatives
  of the HRS.Whole.empirical and the mean-field measure, measurability through pairings);
* `sa6_Xi_norm_le`: the trivial pathwise bound `‖Ξ‖ ≤ 2σ_N|Kad|` (for the finitely many small `N`);
* `sa6_M_L1`, `sa6_core_moment`: `E‖Ξ‖ ≤ (1 + C_in²) + (1 + C_b A²) + (σ_N/2)K' T(𝔈_N + e_N)` for `N ≥ 2` from the
  decomposition `Ξ = I' + M_t + R` (BDG for `M_t`, the pathwise remainder bound).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

lemma sa6_enorm_le_one_add_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 2 := by
  rw [← ofReal_norm_eq_enorm]
  have h : ENNReal.ofReal ‖x‖ ≤ ENNReal.ofReal (1 + ‖x‖ ^ 2) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖x‖ - 1 / 2), norm_nonneg x])
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
  simp

lemma sa6_enorm_le_one_add_pow4 {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 4 := by
  rw [← ofReal_norm_eq_enorm]
  have hx := norm_nonneg x
  have h : ENNReal.ofReal ‖x‖ ≤ ENNReal.ofReal (1 + ‖x‖ ^ 4) := by
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h1 : ‖x‖ ≤ 1
    · nlinarith [pow_nonneg hx 4]
    · push Not at h1
      have : ‖x‖ ≤ ‖x‖ ^ 4 := by
        have h2 : 1 ≤ ‖x‖ ^ 3 := one_le_pow₀ h1.le
        nlinarith [pow_nonneg hx 3]
      nlinarith [pow_nonneg hx 4]
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_pow hx]
  simp

section Exist

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ}
  {C₀ : ℝ} {𝔈 : ℕ → ℝ} {Γ : ℕ} {Kad : ℝ}

theorem sa6_exists_Xi (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (hadjN : AdjointInputOneD (Γ : ℝ) (mStar d) (S.coeff N) S.T Kad) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∃ Ξ : (R N).Ω → HNeg d (Γ : ℝ), Measurable Ξ ∧ IsFluctFieldRepr S R N Γ t Ξ := by
  classical
  have hT : 0 ≤ S.T := S.hT.le
  have hN0 : 0 < N := hN
  have hK : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ x, |φ x| ≤ Kad * HRS.Whole.sobolevNorm (Γ : ℝ) φ :=
    fun φ hφ x => sa6_sob_bound hT hadjN hφ x
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N t)) :=
    Q09A.measure_isProb ((hS.mean_field.solution N hN).density t ht)
  obtain ⟨k₂, hk₂⟩ := sa6_riesz_meas hK (HRS.Whole.withDensityReal (S.ρ N t))
  have hex : ∀ ζ, ∃ k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      HNeg.pairing φ k = S.sigma N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ) := by
    intro ζ
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 ((R N).X (Real.toNNReal t) ζ)
    obtain ⟨k₁, hk₁⟩ := sa6_riesz_meas hK (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ))
    refine ⟨S.sigma N • (k₁ - k₂), fun φ hφ => ?_⟩
    rw [mrm_pairing_smul hφ, mhn_pairing_sub hφ, hk₁ φ hφ, hk₂ φ hφ]
    rfl
  choose Ξ hΞ using hex
  refine ⟨Ξ, ?_, fun φ hφ => ae_of_all _ fun ζ => hΞ ζ φ hφ⟩
  refine mrm_measurable_of_pairings (fun φ hφ => ?_)
  have : (fun ζ => HNeg.pairing φ (Ξ ζ)) = fun ζ => S.sigma N *
      (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ - HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ) := by
    funext ζ; exact hΞ ζ φ hφ
  rw [this]
  exact ((sa6_meas_pair_emp hN0 (Q09A.selectedFlow_measurable (hS.flow N hN) _)
    hφ.1.continuous).sub_const _).const_mul _

theorem sa6_Xi_norm_le (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (hadjN : AdjointInputOneD (Γ : ℝ) (mStar d) (S.coeff N) S.T Kad) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Ξ : (R N).Ω → HNeg d (Γ : ℝ)} (hΞ : IsFluctFieldRepr S R N Γ t Ξ) :
    ∀ᵐ ζ ∂(R N).P, ‖Ξ ζ‖ ≤ 2 * S.sigma N * |Kad| := by
  classical
  have hT : 0 ≤ S.T := S.hT.le
  have hN0 : 0 < N := hN
  have hσ := mrr_sigma_nonneg S N
  obtain ⟨φ, hφt, hφn, hnorm⟩ := hneg_norming d (Γ : ℝ)
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N t)) :=
    Q09A.measure_isProb ((hS.mean_field.solution N hN).density t ht)
  have hK : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ x, |φ x| ≤ |Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) φ :=
    fun φ hφ x => (sa6_sob_bound hT hadjN hφ x).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  have hb : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (n : ℕ),
      |HRS.Whole.pair μ (φ n)| ≤ |Kad| := fun μ _ n => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := φ n)
      (C := |Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) (φ n))
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hK (φ n) (hφt n) x)
    have h2 : |Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) (φ n) ≤ |Kad| :=
      mul_le_of_le_one_right (abs_nonneg _) (hφn n)
    simpa [HRS.Whole.pair, Real.norm_eq_abs] using this.trans (by simpa using h2)
  have hall : ∀ n : ℕ, ∀ᵐ ζ ∂(R N).P, |HNeg.pairing (φ n) (Ξ ζ)| ≤ 2 * S.sigma N * |Kad| := by
    intro n
    filter_upwards [hΞ (φ n) (hφt n)] with ζ h
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 ((R N).X (Real.toNNReal t) ζ)
    rw [h, abs_mul, abs_of_nonneg hσ]
    have h1 := hb (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) n
    have h2 := hb (HRS.Whole.withDensityReal (S.ρ N t)) n
    have h3 : |HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) (φ n) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (φ n)| ≤ 2 * |Kad| := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      exact abs_le.2 ⟨by linarith [a1.1, a2.2], by linarith [a1.2, a2.1]⟩
    calc S.sigma N * |_| ≤ S.sigma N * (2 * |Kad|) := mul_le_mul_of_nonneg_left h3 hσ
      _ = _ := by ring
  filter_upwards [ae_all_iff.2 hall] with ζ hζ
  rw [hnorm (Ξ ζ)]
  exact ciSup_le hζ

end Exist

section MomentM

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {κ : Type} [Fintype κ]

theorem sa6_M_L1 {M : ℝ → Ω → H} {Z : ℝ → Ω → κ → H} {t : ℝ} (ht : 0 ≤ t)
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M (fun r ω => hsCovForm (Z r ω)))
    {B A : ℝ} (hB : 0 ≤ B) (hZ : ∀ r ω k, ‖Z r ω k‖ ≤ B)
    (hA : t * (Fintype.card κ : ℝ) * B ^ 2 ≤ A) :
    ∫⁻ ω, ‖M t ω‖ₑ ∂P ≤ ENNReal.ofReal (1 + mrmCb * A ^ 2) := by
  have hbdg := mrm_bdg_four ht hM
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hin : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) t, ∑ k, ‖Z r ω k‖ₑ ^ 2 ≤ ENNReal.ofReal A := by
    intro ω
    have hpt : ∀ r, ∑ k, ‖Z r ω k‖ₑ ^ 2 ≤ (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r
      calc ∑ k, ‖Z r ω k‖ₑ ^ 2 ≤ ∑ _k : κ, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hZ r ω k)
        _ = _ := by simp
    calc ∫⁻ r in Set.Icc (0 : ℝ) t, ∑ k, ‖Z r ω k‖ₑ ^ 2
        ≤ ∫⁻ _r in Set.Icc (0 : ℝ) t, (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal B ^ 2 :=
          lintegral_mono hpt
      _ = ENNReal.ofReal t * ((Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal B ^ 2) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
          exact mul_comm _ _
      _ = ENNReal.ofReal (t * (Fintype.card κ : ℝ) * B ^ 2) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ht, ENNReal.ofReal_pow hB,
            ENNReal.ofReal_natCast]
          exact (mul_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hA
  have h4 : ∫⁻ ω, ‖M t ω‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal (mrmCb * A ^ 2) := by
    refine hbdg.trans ?_
    rw [ENNReal.ofReal_mul mrmCb_nonneg]
    refine mul_le_mul' le_rfl ?_
    calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ k, ‖Z r ω k‖ₑ ^ 2) ^ 2 ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal A ^ 2 ∂P := lintegral_mono fun ω => pow_le_pow_left' (hin ω) 2
      _ = ENNReal.ofReal (A ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_pow hA0]
  calc ∫⁻ ω, ‖M t ω‖ₑ ∂P ≤ ∫⁻ ω, (1 + ‖M t ω‖ₑ ^ 4) ∂P :=
        lintegral_mono fun ω => sa6_enorm_le_one_add_pow4 _
    _ = 1 + ∫⁻ ω, ‖M t ω‖ₑ ^ 4 ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal (mrmCb * A ^ 2) := add_le_add le_rfl h4
    _ = ENNReal.ofReal (1 + mrmCb * A ^ 2) := by
        rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg mrmCb_nonneg (sq_nonneg _))]
        simp

end MomentM

end HRS.MS.MainRdField
