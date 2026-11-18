import HRS.MS.S11GAux5

/-!
# S11G: Gaussian covariance comparison on a separable Banach space

For centered Gaussian laws `γ₁, γ₂` and a `C²` function `F` with `‖D²F‖ ≤ Mb`, if the covariances differ by at most
`δ` against all norm-one bilinear forms, then `|E_{γ₁}F - E_{γ₂}F| ≤ ½ Mb δ`.  `F` and `DF` may grow (linearly, resp.
quadratically); only the Hessian is bounded.  Proof: rotation interpolation `t ↦ E F(cos t X + sin t Y)`, derivative
`sin t cos t · E[Q₂ - Q₁](Z_t)` by Gaussian integration by parts in each coordinate.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS ProbabilityTheory

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem s11g_integrable_of_hessian {γ : Measure B} (hγ : IsCenteredGaussian γ) {F : B → ℝ}
    (hF : ContDiff ℝ 2 F) {Mb : ℝ} (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) : Integrable F γ := by
  haveI := hγ.1
  have hint1 : Integrable (fun w : B => ‖w‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hint2 := HRS.gaussian_sqnorm_integrable hγ
  have hb : Integrable (fun w : B => ‖F 0‖ + ‖fderiv ℝ F 0‖ * ‖w‖ + Mb * ‖w‖ ^ 2) γ :=
    ((integrable_const _).add (hint1.const_mul _)).add (hint2.const_mul _)
  refine hb.mono' hF.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have := s11g_value_growth hF h2 w
  nlinarith

theorem s11g_gaussian_comparison (γ₁ γ₂ : Measure B) (hg₁ : IsCenteredGaussian γ₁)
    (hg₂ : IsCenteredGaussian γ₂) {F : B → ℝ} (hF : ContDiff ℝ 2 F) {Mb δ : ℝ}
    (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ Mb)
    (hcov : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |(∫ x, M ![x, x] ∂γ₁) - (∫ x, M ![x, x] ∂γ₂)| ≤ δ) :
    Integrable F γ₁ ∧ Integrable F γ₂ ∧
      |(∫ x, F x ∂γ₁) - (∫ x, F x ∂γ₂)| ≤ 1 / 2 * Mb * δ := by
  haveI := hg₁.1
  haveI := hg₂.1
  have h2' : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb := fun w => s11g_fderiv2_bound h2 w
  have hMb : 0 ≤ Mb := (norm_nonneg (iteratedFDeriv ℝ 2 F 0)).trans (h2 0)
  have hδ : 0 ≤ δ := by
    have := hcov 0 (by simp)
    simpa using this
  refine ⟨s11g_integrable_of_hessian hg₁ hF h2', s11g_integrable_of_hessian hg₂ hF h2', ?_⟩
  set μ := γ₁.prod γ₂ with hμ
  set φ : ℝ → ℝ := fun t => ∫ q, F (Zt t q) ∂μ with hφ
  set I : ℝ → ℝ := fun t => ∫ q, (Qγ γ₂ F (Zt t q) - Qγ γ₁ F (Zt t q)) ∂μ with hI
  have hder : ∀ t, HasDerivAt φ (Real.sin t * Real.cos t * I t) t := fun t =>
    (s11g_deriv γ₁ γ₂ hg₁ hg₂ hF h2' t).2
  have hIb : ∀ t, |I t| ≤ Mb * δ := by
    intro t
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := Mb * δ)
      (f := fun q => Qγ γ₂ F (Zt t q) - Qγ γ₁ F (Zt t q))
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact s11g_Q_diff γ₁ γ₂ h2 hcov _)
    simpa [hI, Real.norm_eq_abs] using this
  have hK : 0 ≤ Mb * δ := mul_nonneg hMb hδ
  -- endpoints
  have hint0 := (s11g_deriv γ₁ γ₂ hg₁ hg₂ hF h2' 0).1
  have hint1 := (s11g_deriv γ₁ γ₂ hg₁ hg₂ hF h2' (Real.pi / 2)).1
  have hφ0 : φ 0 = ∫ x, F x ∂γ₁ := by
    simp only [hφ, Zt, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at hint0 ⊢
    rw [hμ, integral_prod _ hint0]
    simp
  have hφ1 : φ (Real.pi / 2) = ∫ x, F x ∂γ₂ := by
    simp only [hφ, Zt, Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, zero_add] at hint1 ⊢
    rw [hμ, integral_prod_symm _ hint1]
    simp
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsc : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin t * Real.cos t := by
    intro t ht
    have h1 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have h2 : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    positivity
  -- upper bound
  have hup : φ (Real.pi / 2) - φ 0 ≤ Mb * δ / 2 := by
    set ψ : ℝ → ℝ := fun t => φ t - (Mb * δ / 2) * Real.sin t ^ 2 with hψ
    have hψd : ∀ t, HasDerivAt ψ (Real.sin t * Real.cos t * (I t - Mb * δ)) t := by
      intro t
      have h1 := (Real.hasDerivAt_sin t).pow 2
      have h2 := (hder t).sub (h1.const_mul (Mb * δ / 2))
      convert h2 using 1
      simp
      ring
    have hanti : AntitoneOn ψ (Set.Icc 0 (Real.pi / 2)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun t _ => (hψd t).continuousAt.continuousWithinAt)
        (fun t _ => (hψd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (hsc t ht) (by linarith [(abs_le.1 (hIb t)).2])
    have := hanti ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
    simp only [hψ, Real.sin_pi_div_two, Real.sin_zero] at this
    nlinarith
  have hlow : φ 0 - φ (Real.pi / 2) ≤ Mb * δ / 2 := by
    set ψ : ℝ → ℝ := fun t => φ t + (Mb * δ / 2) * Real.sin t ^ 2 with hψ
    have hψd : ∀ t, HasDerivAt ψ (Real.sin t * Real.cos t * (I t + Mb * δ)) t := by
      intro t
      have h1 := (Real.hasDerivAt_sin t).pow 2
      have h2 := (hder t).add (h1.const_mul (Mb * δ / 2))
      convert h2 using 1
      simp
      ring
    have hmono : MonotoneOn ψ (Set.Icc 0 (Real.pi / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t _ => (hψd t).continuousAt.continuousWithinAt)
        (fun t _ => (hψd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      exact mul_nonneg (hsc t ht) (by linarith [(abs_le.1 (hIb t)).1])
    have := hmono ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
    simp only [hψ, Real.sin_pi_div_two, Real.sin_zero] at this
    nlinarith
  rw [← hφ0, ← hφ1, abs_le]
  constructor <;> nlinarith

end HRS.MS.S11G
