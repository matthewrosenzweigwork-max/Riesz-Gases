import HRS.MS.S21H2_S30B
import HRS.MS.S21E_Kappa0

/-!
# S21H2, packet R26-T3.S30 (part C): coordinate covariance, cubic tensor, `W_N = Ssum Y N`

* `s21h2_gauss_seq`: the Gaussian with the covariance of `Y#μ` is an `IsCenteredGaussianSeq` with the
  susceptibility covariance at `γ = 0`.
* `s21h2_tensor`: `κ₀ = s21eKappa0 μ Y` lies in `projTensor ℓ² 3` and evaluates as `∫ M(Y x,Y x,Y x) dμ`.
* `s21h2_W_eq`: the feature vector of an iid configuration is `Ssum Y N`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

set_option maxSynthPendingDepth 3

namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d J : ℕ} {q : ℕ → Euc d → ℝ}

theorem s21h2_gauss_seq (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (g : Euc d → ℝ) (G : Measure SeqL2) [IsProbabilityMeasure G]
    (hg : IsCenteredGaussian G)
    (hcov : ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (s21h2_Y q μ)) x y) :
    IsCenteredGaussianSeq G (fun i j => HRS.Whole.susceptibilityCov g μ 0 (q i) (q j)) := by
  refine ⟨hg, fun i j => ?_⟩
  haveI := hg.1
  have hcont := s21h2_continuous hq μ
  obtain ⟨C, hC⟩ := s21h2_norm_le hq μ
  have hYae : AEMeasurable (s21h2_Y q μ) μ := hcont.aemeasurable
  have hYL : MemLp (s21h2_Y q μ) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
  have hn : Integrable (fun z : SeqL2 => ‖z‖ ^ 2) G := by
    have := hmem.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  set a : SeqL2 := S45.s45_seqBasis i with ha
  set b : SeqL2 := S45.s45_seqBasis j with hb
  have hna : ‖a‖ = 1 := (S45.s45_seqBasis.orthonormal.norm_eq_one i)
  have hnb : ‖b‖ = 1 := (S45.s45_seqBasis.orthonormal.norm_eq_one j)
  have hca : ∀ F : SeqL2, SeqL2.coord F i = inner ℝ a F := fun F => (S45.s45_inner_seqBasis i F).symm
  have hcb : ∀ F : SeqL2, SeqL2.coord F j = inner ℝ b F := fun F => (S45.s45_inner_seqBasis j F).symm
  simp_rw [hca, hcb]
  have hint : Integrable (fun F : SeqL2 => inner ℝ a F * inner ℝ b F) G := by
    refine (hn.const_mul (‖a‖ * ‖b‖)).mono' ?_ (Filter.Eventually.of_forall fun F => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a F‖ * ‖inner ℝ b F‖ ≤ (‖a‖ * ‖F‖) * (‖b‖ * ‖F‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
              (by positivity)
        _ = ‖a‖ * ‖b‖ * ‖F‖ ^ 2 := by ring
  refine ⟨hint, ?_⟩
  have h1 : ∫ F, inner ℝ a F * inner ℝ b F ∂G = covarianceBilin G a b := by
    rw [covarianceBilin_apply hmem, HRS.HilbertCLTAux.gaussian_mean_zero hg]
    simp
  have hmemY : MemLp id 2 (μ.map (s21h2_Y q μ)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hYae).mpr hYL
  have hmean : (μ.map (s21h2_Y q μ))[id] = 0 := by
    show ∫ z, id z ∂(μ.map (s21h2_Y q μ)) = 0
    rw [integral_map hYae aestronglyMeasurable_id]
    exact s21h2_centered hq μ
  have h2 : covarianceBilin (μ.map (s21h2_Y q μ)) a b =
      ∫ x, inner ℝ a (s21h2_Y q μ x) * inner ℝ b (s21h2_Y q μ x) ∂μ := by
    rw [covarianceBilin_apply hmemY, hmean]
    simp only [sub_zero]
    rw [integral_map hYae (by fun_prop)]
  rw [h1, hcov, h2, s21h2_susc hq μ g i j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [ha, hb, s21h2_inner hq μ, s21h2_inner hq μ]

theorem s21h2_tensor (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : ∃ K : projTensor SeqL2 3,
    (K : TensorDual SeqL2 3) = HRS.MS.S21E.s21eKappa0 μ (s21h2_Y q μ) ∧
    ∀ T : SeqL2 [×3]→L[ℝ] ℝ, (K : TensorDual SeqL2 3) T = ∫ x, T ![s21h2_Y q μ x, s21h2_Y q μ x, s21h2_Y q μ x] ∂μ := by
  have hcont := s21h2_continuous hq μ
  obtain ⟨C, hC⟩ := s21h2_norm_le hq μ
  have hasm : AEStronglyMeasurable (s21h2_Y q μ) μ := hcont.aestronglyMeasurable
  have hint : Integrable (fun x => ‖s21h2_Y q μ x‖ * ‖s21h2_Y q μ x‖ * ‖s21h2_Y q μ x‖) μ := by
    refine Integrable.of_bound (C := C * C * C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hcont.norm.mul hcont.norm).mul hcont.norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖s21h2_Y q μ x‖ := norm_nonneg _
      have h1 := hC x
      have hC0 : 0 ≤ C := h0.trans h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  exact ⟨⟨_, HRS.MS.S21E.s21e_kappa0_mem μ hasm hint⟩, rfl, fun T =>
    HRS.MS.S21E.s21e_kappa0_apply μ hasm hint T⟩

theorem s21h2_marg_pi (N : ℕ) (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    HRS.Whole.firstMarginal (Measure.pi fun _ : Fin N => μ) = μ := by
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (by omega : 0 < N)]
  have h := Measure.pi_map_eval (μ := fun _ : Fin N => μ) (⟨0, by omega⟩ : Fin N)
  simpa using h

theorem s21h2_W_eq (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N) (z : EucConfig d N) :
    featureVec q μ z = HRS.StaticLimitAux.Ssum (s21h2_Y q μ) N z := by
  have hN0 : 0 < N := hN
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  refine lp.ext (funext fun j => ?_)
  have e1 : SeqL2.coord (featureVec q μ z) j =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical z) (q j) - HRS.Whole.pair μ (q j)) := by
    unfold featureVec
    exact S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN hq (ν := μ) z) j
  have e2 : SeqL2.coord (HRS.StaticLimitAux.Ssum (s21h2_Y q μ) N z) j =
      (Real.sqrt N)⁻¹ * ∑ i, (q j (z i) - HRS.Whole.pair μ (q j)) := by
    rw [← S45.s45_inner_seqBasis, HRS.StaticLimitAux.Ssum, inner_smul_right, inner_sum]
    simp_rw [s21h2_inner hq μ]
  show SeqL2.coord (featureVec q μ z) j = SeqL2.coord (HRS.StaticLimitAux.Ssum (s21h2_Y q μ) N z) j
  rw [e1, e2, HRS.Whole.pair_empirical hN0, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  generalize Real.sqrt (N : ℝ) = r at hr hr0 ⊢
  rw [← hr]
  field_simp

end HRS.MS.R26T3
