import HRS.MS.S21H2_S30A

/-!
# S21H2, packet R26-T3.S30 (part B): continuity, centering, Gaussian and covariance of `Y`

`Y = s21h2_Y q μ` is continuous and `μ`-centered; the centered Gaussian `G` on `ℓ²` with the covariance of `Y#μ`
exists (trace-class covariance) and has coordinate covariances `μ((q_i - μ q_i)(q_j - μ q_j))
 = susceptibilityCov _ μ 0 (q i) (q j)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d J : ℕ} {q : ℕ → Euc d → ℝ}

theorem s21h2_continuous (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Continuous (s21h2_Y q μ) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hdiff : ∀ x, ‖s21h2_Y q μ x - s21h2_Y q μ y‖ ^ 2 = ∑' j, (q j x - q j y) ^ 2 := by
    intro x
    rw [← u11_norm_sq]
    refine tsum_congr fun j => ?_
    rw [u11_coord_sub, s21h2_coord hq, s21h2_coord hq]
    ring_nf
  have hF : Continuous fun x => ∑' j, (q j x - q j y) ^ 2 := by
    refine continuous_tsum (u := fun j => (2 * cbNorm J (q j)) ^ 2)
      (fun j => ((hq.1 j).1.continuous.sub continuous_const).pow 2) (s21h2_summable_sq hq)
      (fun j x => ?_)
    have h3 : |q j x - q j y| ≤ 2 * cbNorm J (q j) := by
      have hx := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) x
      have hy := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) y
      rw [Real.norm_eq_abs] at hx hy
      exact (abs_sub _ _).trans (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have h0 : (∑' j, (q j y - q j y) ^ 2) = 0 := by simp
  have hT : Tendsto (fun x => ‖s21h2_Y q μ x - s21h2_Y q μ y‖) (𝓝 y) (𝓝 0) := by
    have hfun : (fun x => ‖s21h2_Y q μ x - s21h2_Y q μ y‖) =
        fun x => Real.sqrt (∑' j, (q j x - q j y) ^ 2) := by
      funext x
      rw [← hdiff, Real.sqrt_sq (norm_nonneg _)]
    rw [hfun]
    have := ((Real.continuous_sqrt.comp hF).continuousAt (x := y)).tendsto
    rw [show (0 : ℝ) = Real.sqrt (∑' j, (q j y - q j y) ^ 2) by simp [h0]]
    exact this
  exact tendsto_iff_norm_sub_tendsto_zero.2 hT

theorem s21h2_integrable (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Integrable (s21h2_Y q μ) μ := by
  obtain ⟨C, hC⟩ := s21h2_norm_le hq μ
  exact Integrable.of_bound (s21h2_continuous hq μ).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem s21h2_centered (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : ∫ x, s21h2_Y q μ x ∂μ = 0 := by
  have hint := s21h2_integrable hq μ
  have hco : ∀ j, inner ℝ (S45.s45_seqBasis j) (∫ x, s21h2_Y q μ x ∂μ) = 0 := by
    intro j
    rw [← integral_inner hint]
    simp_rw [s21h2_inner hq μ]
    have hi : Integrable (q j) μ :=
      Integrable.of_bound (hq.1 j).1.continuous.aestronglyMeasurable (cbNorm J (q j))
        (Filter.Eventually.of_forall fun y => HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) y)
    rw [integral_sub hi (integrable_const _)]
    simp [HRS.Whole.pair]
  refine lp.ext (funext fun j => ?_)
  have := hco j
  rw [S45.s45_inner_seqBasis] at this
  exact this

theorem s21h2_exists_gaussian (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : ∃ G : Measure SeqL2, IsProbabilityMeasure G ∧
    IsCenteredGaussian G ∧
    ∀ x y, covarianceBilin G x y = covarianceBilin (μ.map (s21h2_Y q μ)) x y := by
  obtain ⟨C, hC⟩ := s21h2_norm_le hq μ
  have hYL : MemLp (s21h2_Y q μ) 2 μ :=
    MemLp.of_bound (s21h2_continuous hq μ).aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  obtain ⟨htc, -⟩ := HRS.isTraceClassCov_covarianceBilin μ (s21h2_Y q μ) hYL (s21h2_centered hq μ)
  obtain ⟨γ, hp, hg, hcov⟩ := HRS.exists_centeredGaussian_of_traceClass _ htc
  exact ⟨γ, hp, hg, hcov⟩

theorem s21h2_susc (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (g : Euc d → ℝ) (i j : ℕ) :
    HRS.Whole.susceptibilityCov g μ 0 (q i) (q j) =
      ∫ x, (q i x - HRS.Whole.pair μ (q i)) * (q j x - HRS.Whole.pair μ (q j)) ∂μ := by
  have h := s11iid_resp_ae μ g (hq.1 j).1.continuous (C := cbNorm J (q j)) (fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) x
    rwa [Real.norm_eq_abs] at this)
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]
  simp [HRS.Whole.projMean, HRS.Whole.pair]

end HRS.MS.R26T3
