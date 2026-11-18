import HRS.MS.S11GAux3
import HRS.Prob.Metrics

/-!
# S11G: the Hessian contraction and the covariance bound, pointwise
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS ProbabilityTheory

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem s11g_Q_bound (γ : Measure B) (hγ : IsCenteredGaussian γ) {F : B → ℝ} {Mb : ℝ}
    (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) (w : B) :
    |Qγ γ F w| ≤ Mb * ∫ z, ‖z‖ ^ 2 ∂γ := by
  haveI := hγ.1
  have hMb : 0 ≤ Mb := (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)).trans (h2 0)
  have hint2 := HRS.gaussian_sqnorm_integrable hγ
  unfold Qγ
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hint2.const_mul Mb) (Filter.Eventually.of_forall fun z => ?_)).trans
    (le_of_eq (integral_const_mul _ _))
  refine ((fderiv ℝ (fderiv ℝ F) w z).le_opNorm z).trans ?_
  have : ‖fderiv ℝ (fderiv ℝ F) w z‖ ≤ Mb * ‖z‖ :=
    ((fderiv ℝ (fderiv ℝ F) w).le_opNorm z).trans (mul_le_mul_of_nonneg_right (h2 w) (norm_nonneg z))
  calc _ ≤ Mb * ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg z)
    _ = _ := by ring

theorem s11g_Q_continuous (γ : Measure B) (hγ : IsCenteredGaussian γ) {F : B → ℝ}
    (hF : ContDiff ℝ 2 F) {Mb : ℝ} (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) :
    Continuous (Qγ γ F) := by
  haveI := hγ.1
  have hMb : 0 ≤ Mb := (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)).trans (h2 0)
  have hint2 := HRS.gaussian_sqnorm_integrable hγ
  have hd2 : Continuous (fderiv ℝ (fderiv ℝ F)) := by
    have : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact this.continuous_fderiv (by norm_num)
  unfold Qγ
  refine continuous_of_dominated (bound := fun z => Mb * ‖z‖ ^ 2) (fun w => ?_) (fun w => ?_)
    (hint2.const_mul Mb) (Filter.Eventually.of_forall fun z => ?_)
  · have : Continuous fun z : B => fderiv ℝ (fderiv ℝ F) w z z :=
      ((fderiv ℝ (fderiv ℝ F) w).continuous.clm_apply continuous_id)
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have : ‖fderiv ℝ (fderiv ℝ F) w z‖ ≤ Mb * ‖z‖ :=
      ((fderiv ℝ (fderiv ℝ F) w).le_opNorm z).trans (mul_le_mul_of_nonneg_right (h2 w) (norm_nonneg z))
    refine ((fderiv ℝ (fderiv ℝ F) w z).le_opNorm z).trans ?_
    calc _ ≤ Mb * ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg z)
      _ = _ := by ring
  · exact (hd2.clm_apply continuous_const).clm_apply continuous_const

/-- The covariance bound transferred to the Hessian contractions. -/
theorem s11g_Q_diff (γ₁ γ₂ : Measure B) {F : B → ℝ} {Mb δ : ℝ}
    (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ Mb)
    (hcov : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |(∫ x, M ![x, x] ∂γ₁) - (∫ x, M ![x, x] ∂γ₂)| ≤ δ) (w : B) :
    |Qγ γ₂ F w - Qγ γ₁ F w| ≤ Mb * δ := by
  have hMb : 0 ≤ Mb := (norm_nonneg (iteratedFDeriv ℝ 2 F 0)).trans (h2 0)
  have hδ : 0 ≤ δ := by
    have := hcov 0 (by simp)
    simpa using this
  have hQ : ∀ γ : Measure B, Qγ γ F w = ∫ z, iteratedFDeriv ℝ 2 F w ![z, z] ∂γ := by
    intro γ
    unfold Qγ
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [iteratedFDeriv_two_apply]
  rw [hQ, hQ]
  set M := iteratedFDeriv ℝ 2 F w with hM
  have hn : ‖M‖ ≤ Mb := h2 w
  by_cases h0 : ‖M‖ = 0
  · have : M = 0 := norm_eq_zero.1 h0
    rw [this]
    simp only [ContinuousMultilinearMap.zero_apply, integral_zero, sub_zero, abs_zero]
    positivity
  · have hpos : 0 < ‖M‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 := hcov ((‖M‖⁻¹) • M) (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0])
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, integral_const_mul] at h1
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hpos)] at h1
    have h3 : |(∫ x, M ![x, x] ∂γ₁) - ∫ x, M ![x, x] ∂γ₂| ≤ ‖M‖ * δ := by
      have := mul_le_mul_of_nonneg_left h1 hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ h0, one_mul] at this
    rw [abs_sub_comm]
    exact h3.trans (mul_le_mul_of_nonneg_right hn hδ)

end HRS.MS.S11G
