import HRS.Prob.Gaussian

/-!
# Packet GT (row 7.14), core: the derivative of the Gaussian interpolation

For centred Gaussian laws `γ₁, γ₂` on a separable Banach space and `Φ ∈ C²` with bounded first and second
derivatives, the function `θ ↦ ∫ Φ(cos θ x + sin θ y) d(γ₁ ⊗ γ₂)` has derivative
`sin θ cos θ ∫ (Q₂Φ - Q₁Φ)(cos θ x + sin θ y) d(γ₁ ⊗ γ₂)` where `Q_i Φ (u) = ∫ D²Φ(u)[z,z] dγ_i(z)`.
Proof: differentiation under the integral and the Banach-space Gaussian integration by parts `gaussian_ibp`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.Q714.GT

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- The interpolation point `cos θ x + sin θ y`. -/
def gtPt (θ : ℝ) (q : B × B) : B := Real.cos θ • q.1 + Real.sin θ • q.2

lemma gtPt_cont (θ : ℝ) : Continuous (gtPt (B := B) θ) := by
  unfold gtPt; fun_prop

lemma gtPt_zero (q : B × B) : gtPt 0 q = q.1 := by simp [gtPt]

lemma gtPt_pi_div_two (q : B × B) : gtPt (Real.pi / 2) q = q.2 := by simp [gtPt]

/-- The second moment functional `u ↦ ∫ D²Φ(u)[z,z] dγ(z)`. -/
def gtQ (γ : Measure B) (Φ : B → ℝ) (u : B) : ℝ := ∫ z, fderiv ℝ (fderiv ℝ Φ) u z z ∂γ

lemma gt_D2_bound {Φ : B → ℝ} {M2 : ℝ} (hM2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2) (u z : B) :
    ‖fderiv ℝ (fderiv ℝ Φ) u z z‖ ≤ M2 * ‖z‖ ^ 2 := by
  refine ((fderiv ℝ (fderiv ℝ Φ) u z).le_opNorm z).trans ?_
  have h1 : ‖fderiv ℝ (fderiv ℝ Φ) u z‖ ≤ M2 * ‖z‖ :=
    ((fderiv ℝ (fderiv ℝ Φ) u).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hM2 u) (norm_nonneg _))
  calc _ ≤ M2 * ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := by ring

lemma gt_D2_cont {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ) :
    Continuous (fderiv ℝ (fderiv ℝ Φ)) := by
  have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  exact this.continuous_fderiv (by norm_num)

lemma gt_D2_zcont {Φ : B → ℝ} (u : B) :
    Continuous (fun z : B => fderiv ℝ (fderiv ℝ Φ) u z z) :=
  (fderiv ℝ (fderiv ℝ Φ) u).continuous.clm_apply continuous_id

lemma gt_D2_int {γ : Measure B} [IsFiniteMeasure γ] (hint2 : Integrable (fun z : B => ‖z‖ ^ 2) γ)
    {Φ : B → ℝ} {M2 : ℝ} (hM2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2) (u : B) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ Φ) u z z) γ :=
  (hint2.const_mul M2).mono' (gt_D2_zcont u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => gt_D2_bound hM2 u z)

lemma gtQ_cont {γ : Measure B} [IsFiniteMeasure γ] (hint2 : Integrable (fun z : B => ‖z‖ ^ 2) γ)
    {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ) {M2 : ℝ} (hM2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2) :
    Continuous (gtQ γ Φ) := by
  have hd2 := gt_D2_cont hΦ
  refine continuous_of_dominated (bound := fun z => M2 * ‖z‖ ^ 2)
    (fun u => (gt_D2_zcont u).aestronglyMeasurable)
    (fun u => Filter.Eventually.of_forall fun z => gt_D2_bound hM2 u z)
    (hint2.const_mul M2) (Filter.Eventually.of_forall fun z => ?_)
  exact (hd2.clm_apply continuous_const).clm_apply continuous_const

lemma gtQ_bound {γ : Measure B} [IsFiniteMeasure γ] (hint2 : Integrable (fun z : B => ‖z‖ ^ 2) γ)
    {Φ : B → ℝ} {M2 : ℝ} (hM2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2) (u : B) :
    |gtQ γ Φ u| ≤ M2 * ∫ z, ‖z‖ ^ 2 ∂γ := by
  have := norm_integral_le_of_norm_le (hint2.const_mul M2)
    (Filter.Eventually.of_forall fun z => gt_D2_bound hM2 u z)
  rw [integral_const_mul] at this
  simpa [gtQ] using this

lemma gt_norm_vec_le (θ : ℝ) (q : B × B) :
    ‖(-Real.sin θ) • q.1 + Real.cos θ • q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, norm_neg, Real.norm_eq_abs]
  have a1 := Real.abs_sin_le_one θ
  have a2 := Real.abs_cos_le_one θ
  nlinarith [norm_nonneg q.1, norm_nonneg q.2]

/-- The derivative of the Gaussian interpolation, for `Φ ∈ C²` with bounded `Φ`, `DΦ`, `D²Φ`. -/
lemma gt_hasDerivAt {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (h₁ : IsCenteredGaussian γ₁) (h₂ : IsCenteredGaussian γ₂) {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {M0 M1 M2 : ℝ} (hM0 : ∀ w, |Φ w| ≤ M0) (hM1 : ∀ w, ‖fderiv ℝ Φ w‖ ≤ M1)
    (hM2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2) (θ : ℝ) :
    HasDerivAt (fun θ => ∫ q, Φ (gtPt θ q) ∂(γ₁.prod γ₂))
      (Real.sin θ * Real.cos θ *
        ∫ q, (gtQ γ₂ Φ (gtPt θ q) - gtQ γ₁ Φ (gtPt θ q)) ∂(γ₁.prod γ₂)) θ := by
  have hd1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
  have hd2 := gt_D2_cont hΦ
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hM1' : 0 ≤ M1 := (norm_nonneg (fderiv ℝ Φ 0)).trans (hM1 0)
  have hi1 : Integrable (fun w : B => ‖w‖) γ₁ := by
    haveI := h₁.1; exact (IsGaussian.integrable_id (μ := γ₁)).norm
  have hi2 : Integrable (fun w : B => ‖w‖) γ₂ := by
    haveI := h₂.1; exact (IsGaussian.integrable_id (μ := γ₂)).norm
  have hs1 := gaussian_sqnorm_integrable h₁
  have hs2 := gaussian_sqnorm_integrable h₂
  set μ := γ₁.prod γ₂ with hμ
  have hn1 : Integrable (fun q : B × B => ‖q.1‖) μ := hi1.comp_fst γ₂
  have hn2 : Integrable (fun q : B × B => ‖q.2‖) μ := hi2.comp_snd γ₁
  let F : ℝ → B × B → ℝ := fun θ q => Φ (gtPt θ q)
  let F' : ℝ → B × B → ℝ := fun θ q =>
    fderiv ℝ Φ (gtPt θ q) ((-Real.sin θ) • q.1 + Real.cos θ • q.2)
  have hFcont : ∀ θ, Continuous (F θ) := fun θ => hΦc.comp (gtPt_cont θ)
  have hF'cont : ∀ θ, Continuous (F' θ) := fun θ => by
    simp only [F', gtPt]
    exact (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  have hderivF : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => F θ q) (F' θ q) θ := by
    intro θ q
    have h1 := ((Real.hasDerivAt_cos θ).smul_const q.1).add ((Real.hasDerivAt_sin θ).smul_const q.2)
    exact (hΦd (gtPt θ q)).hasFDerivAt.comp_hasDerivAt θ h1
  have hF'bound : ∀ θ q, ‖F' θ q‖ ≤ M1 * (‖q.1‖ + ‖q.2‖) := fun θ q =>
    ((fderiv ℝ Φ (gtPt θ q)).le_opNorm _).trans
      (mul_le_mul (hM1 _) (gt_norm_vec_le θ q) (norm_nonneg _) hM1')
  have hbint : Integrable (fun q : B × B => M1 * (‖q.1‖ + ‖q.2‖)) μ :=
    (hn1.add hn2).const_mul M1
  have hFint : Integrable (F θ) μ :=
    Integrable.of_bound (C := M0) (hFcont θ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hM0 _)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := θ) (bound := fun q => M1 * (‖q.1‖ + ‖q.2‖)) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun θ => (hFcont θ).aestronglyMeasurable) hFint
    (hF'cont θ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q θ _ => hF'bound θ q) hbint
    (Filter.Eventually.of_forall fun q θ _ => hderivF θ q)
  refine HasDerivAt.congr_deriv hD.2 ?_
  -- evaluation of `∫ F' θ`
  have hF'eq : ∀ q, F' θ q = -Real.sin θ * fderiv ℝ Φ (gtPt θ q) q.1 +
      Real.cos θ * fderiv ℝ Φ (gtPt θ q) q.2 := by
    intro q
    simp only [F', map_add, map_smul, smul_eq_mul]
  have hA1c : Continuous fun q : B × B => fderiv ℝ Φ (gtPt θ q) q.1 :=
    (hd1.comp (gtPt_cont θ)).clm_apply continuous_fst
  have hA2c : Continuous fun q : B × B => fderiv ℝ Φ (gtPt θ q) q.2 :=
    (hd1.comp (gtPt_cont θ)).clm_apply continuous_snd
  have hA1i : Integrable (fun q : B × B => fderiv ℝ Φ (gtPt θ q) q.1) μ :=
    (hn1.const_mul M1).mono' hA1c.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
      ((fderiv ℝ Φ (gtPt θ q)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hM1 _) (norm_nonneg _)))
  have hA2i : Integrable (fun q : B × B => fderiv ℝ Φ (gtPt θ q) q.2) μ :=
    (hn2.const_mul M1).mono' hA2c.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
      ((fderiv ℝ Φ (gtPt θ q)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hM1 _) (norm_nonneg _)))
  have hQ1c : Continuous fun q : B × B => gtQ γ₁ Φ (gtPt θ q) :=
    (gtQ_cont hs1 hΦ hM2).comp (gtPt_cont θ)
  have hQ2c : Continuous fun q : B × B => gtQ γ₂ Φ (gtPt θ q) :=
    (gtQ_cont hs2 hΦ hM2).comp (gtPt_cont θ)
  have hQ1i : Integrable (fun q : B × B => gtQ γ₁ Φ (gtPt θ q)) μ :=
    Integrable.of_bound (C := M2 * ∫ z, ‖z‖ ^ 2 ∂γ₁) hQ1c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact gtQ_bound hs1 hM2 _)
  have hQ2i : Integrable (fun q : B × B => gtQ γ₂ Φ (gtPt θ q)) μ :=
    Integrable.of_bound (C := M2 * ∫ z, ‖z‖ ^ 2 ∂γ₂) hQ2c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact gtQ_bound hs2 hM2 _)
  -- the two integrations by parts
  have hI2 : ∫ q, fderiv ℝ Φ (gtPt θ q) q.2 ∂μ = Real.sin θ * ∫ q, gtQ γ₂ Φ (gtPt θ q) ∂μ := by
    rw [integral_prod _ hA2i, integral_prod _ hQ2i, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact gaussian_ibp h₂ hΦ hM1 hM2 (Real.cos θ • x) (Real.sin θ)
  have hI1 : ∫ q, fderiv ℝ Φ (gtPt θ q) q.1 ∂μ = Real.cos θ * ∫ q, gtQ γ₁ Φ (gtPt θ q) ∂μ := by
    rw [integral_prod_symm _ hA1i, integral_prod_symm _ hQ1i, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have := gaussian_ibp h₁ hΦ hM1 hM2 (Real.sin θ • y) (Real.cos θ)
    simp only [gtPt, add_comm (Real.sin θ • y)] at this ⊢
    exact this
  simp_rw [hF'eq]
  rw [integral_add (hA1i.const_mul _) (hA2i.const_mul _), integral_const_mul, integral_const_mul,
    hI1, hI2, integral_sub hQ2i hQ1i]
  ring

end HRS.MC.Q714.GT

end
