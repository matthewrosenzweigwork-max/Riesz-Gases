import HRS.MS.S11GAux4

/-!
# S11G: derivative of the rotation interpolation `t ↦ E F(cos t X + sin t Y)`
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS ProbabilityTheory

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- The rotation `Z_t = cos t · x + sin t · y`. -/
def Zt (t : ℝ) (q : B × B) : B := Real.cos t • q.1 + Real.sin t • q.2

/-- Its derivative in `t`. -/
def Zt' (t : ℝ) (q : B × B) : B := -Real.sin t • q.1 + Real.cos t • q.2

theorem s11g_norm_Zt (t : ℝ) (q : B × B) : ‖Zt t q‖ ≤ ‖q.1‖ + ‖q.2‖ := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs]
  have a1 := Real.abs_sin_le_one t
  have a2 := Real.abs_cos_le_one t
  nlinarith [norm_nonneg q.1, norm_nonneg q.2]

theorem s11g_norm_Zt' (t : ℝ) (q : B × B) : ‖Zt' t q‖ ≤ ‖q.1‖ + ‖q.2‖ := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, norm_neg, Real.norm_eq_abs]
  have a1 := Real.abs_sin_le_one t
  have a2 := Real.abs_cos_le_one t
  nlinarith [norm_nonneg q.1, norm_nonneg q.2]

theorem s11g_hasDerivAt_Zt (q : B × B) (t : ℝ) : HasDerivAt (fun t => Zt t q) (Zt' t q) t := by
  have h1 := ((Real.hasDerivAt_cos t).smul_const q.1).add ((Real.hasDerivAt_sin t).smul_const q.2)
  exact h1

theorem s11g_continuous_Zt (t : ℝ) : Continuous fun q : B × B => Zt t q := by
  unfold Zt; fun_prop

theorem s11g_continuous_Zt_t (q : B × B) : Continuous fun t : ℝ => Zt t q := by
  unfold Zt; fun_prop

theorem s11g_deriv (γ₁ γ₂ : Measure B) (hg₁ : IsCenteredGaussian γ₁) (hg₂ : IsCenteredGaussian γ₂)
    {F : B → ℝ} (hF : ContDiff ℝ 2 F) {Mb : ℝ} (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) (t : ℝ) :
    Integrable (fun q : B × B => F (Zt t q)) (γ₁.prod γ₂) ∧
    HasDerivAt (fun t => ∫ q, F (Zt t q) ∂(γ₁.prod γ₂))
      (Real.sin t * Real.cos t * ∫ q, (Qγ γ₂ F (Zt t q) - Qγ γ₁ F (Zt t q)) ∂(γ₁.prod γ₂)) t := by
  haveI := hg₁.1
  haveI := hg₂.1
  set μ := γ₁.prod γ₂ with hμ
  have hMb : 0 ≤ Mb := (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)).trans (h2 0)
  have hd1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hcF : Continuous F := hF.continuous
  have hdiffF : Differentiable ℝ F := hF.differentiable (by norm_num)
  set a0 : ℝ := ‖fderiv ℝ F 0‖ with ha0
  have ha00 : 0 ≤ a0 := norm_nonneg _
  have hint1₁ : Integrable (fun w : B => ‖w‖) γ₁ := (IsGaussian.integrable_id (μ := γ₁)).norm
  have hint1₂ : Integrable (fun w : B => ‖w‖) γ₂ := (IsGaussian.integrable_id (μ := γ₂)).norm
  have hint2₁ := HRS.gaussian_sqnorm_integrable hg₁
  have hint2₂ := HRS.gaussian_sqnorm_integrable hg₂
  have hSint : Integrable (fun q : B × B => ‖q.1‖ + ‖q.2‖) μ :=
    (hint1₁.comp_fst γ₂).add (hint1₂.comp_snd γ₁)
  have hS2int : Integrable (fun q : B × B => (‖q.1‖ + ‖q.2‖) ^ 2) μ := by
    have := ((hint2₁.comp_fst γ₂).add ((hint1₁.mul_prod hint1₂).const_mul 2)).add (hint2₂.comp_snd γ₁)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    ring
  set S : B × B → ℝ := fun q => ‖q.1‖ + ‖q.2‖ with hS
  -- bounds
  set bF : B × B → ℝ := fun q => ‖F 0‖ + a0 * S q + Mb * S q ^ 2 with hbF
  set b : B × B → ℝ := fun q => a0 * S q + Mb * S q ^ 2 with hb
  have hbFint : Integrable bF μ :=
    ((integrable_const _).add (hSint.const_mul a0)).add (hS2int.const_mul Mb)
  have hbint : Integrable b μ := (hSint.const_mul a0).add (hS2int.const_mul Mb)
  have hDF : ∀ w, ‖fderiv ℝ F w‖ ≤ a0 + Mb * ‖w‖ := s11g_fderiv_growth hF h2
  have hFbound : ∀ (t : ℝ) (q : B × B), ‖F (Zt t q)‖ ≤ bF q := by
    intro t q
    have h1 := s11g_value_growth hF h2 (Zt t q)
    have h2' := s11g_norm_Zt t q
    have h3 : (a0 + Mb * ‖Zt t q‖) * ‖Zt t q‖ ≤ (a0 + Mb * S q) * S q := by
      refine mul_le_mul (by linarith [mul_le_mul_of_nonneg_left h2' hMb]) h2' (norm_nonneg _) (by
        have : 0 ≤ S q := by positivity
        positivity)
      
    simp only [hbF]
    nlinarith
  have hF'bound : ∀ (t : ℝ) (q : B × B), ‖fderiv ℝ F (Zt t q) (Zt' t q)‖ ≤ b q := by
    intro t q
    have h2' := s11g_norm_Zt t q
    have h3 := s11g_norm_Zt' t q
    refine ((fderiv ℝ F (Zt t q)).le_opNorm _).trans ?_
    have hSq : 0 ≤ S q := by positivity
    calc ‖fderiv ℝ F (Zt t q)‖ * ‖Zt' t q‖ ≤ (a0 + Mb * S q) * S q :=
          mul_le_mul ((hDF _).trans (by linarith [mul_le_mul_of_nonneg_left h2' hMb])) h3
            (norm_nonneg _) (by positivity)
      _ = b q := by simp only [hb]; ring
  have hFmeas : ∀ t, AEStronglyMeasurable (fun q : B × B => F (Zt t q)) μ := fun t =>
    (hcF.comp (s11g_continuous_Zt t)).aestronglyMeasurable
  have hFint : ∀ t, Integrable (fun q : B × B => F (Zt t q)) μ := fun t =>
    hbFint.mono' (hFmeas t) (Filter.Eventually.of_forall fun q => hFbound t q)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t q => F (Zt t q)) (F' := fun t q => fderiv ℝ F (Zt t q) (Zt' t q))
    (x₀ := t) (bound := b) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall hFmeas) (hFint t)
    (by
      have : Continuous fun q : B × B => fderiv ℝ F (Zt t q) (Zt' t q) := by
        unfold Zt Zt'
        exact (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
      exact this.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q t _ => hF'bound t q) hbint
    (Filter.Eventually.of_forall fun q t _ => (hdiffF (Zt t q)).hasFDerivAt.comp_hasDerivAt t
      (s11g_hasDerivAt_Zt q t))
  refine ⟨hFint t, ?_⟩
  convert hD.2 using 1
  -- integrability of the two pieces
  have hcont1 : Continuous fun q : B × B => fderiv ℝ F (Zt t q) q.1 :=
    (hd1.comp (s11g_continuous_Zt t)).clm_apply continuous_fst
  have hcont2 : Continuous fun q : B × B => fderiv ℝ F (Zt t q) q.2 :=
    (hd1.comp (s11g_continuous_Zt t)).clm_apply continuous_snd
  have hbd : ∀ (q : B × B) (v : B), ‖v‖ ≤ S q → ‖fderiv ℝ F (Zt t q) v‖ ≤ b q := by
    intro q v hv
    have h2' := s11g_norm_Zt t q
    refine ((fderiv ℝ F (Zt t q)).le_opNorm _).trans ?_
    have hSq : 0 ≤ S q := by positivity
    calc ‖fderiv ℝ F (Zt t q)‖ * ‖v‖ ≤ (a0 + Mb * S q) * S q :=
          mul_le_mul ((hDF _).trans (by linarith [mul_le_mul_of_nonneg_left h2' hMb])) hv
            (norm_nonneg _) (by positivity)
      _ = b q := by simp only [hb]; ring
  have hint_a : Integrable (fun q : B × B => fderiv ℝ F (Zt t q) q.1) μ :=
    hbint.mono' hcont1.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
      hbd q _ (by simp only [hS]; linarith [norm_nonneg q.2]))
  have hint_b : Integrable (fun q : B × B => fderiv ℝ F (Zt t q) q.2) μ :=
    hbint.mono' hcont2.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
      hbd q _ (by simp only [hS]; linarith [norm_nonneg q.1]))
  -- the Hessian contractions are bounded and continuous
  have hQ1c := s11g_Q_continuous γ₁ hg₁ hF h2
  have hQ2c := s11g_Q_continuous γ₂ hg₂ hF h2
  have hQint : ∀ (γ : Measure B) (hg : IsCenteredGaussian γ),
      Integrable (fun q : B × B => Qγ γ F (Zt t q)) μ := by
    intro γ hg
    exact Integrable.of_bound ((s11g_Q_continuous γ hg hF h2).comp (s11g_continuous_Zt t)).aestronglyMeasurable
      (Mb * ∫ z, ‖z‖ ^ 2 ∂γ) (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact s11g_Q_bound γ hg h2 _)
  have hA : ∫ q, fderiv ℝ F (Zt t q) q.1 ∂μ = Real.cos t * ∫ q, Qγ γ₁ F (Zt t q) ∂μ := by
    rw [hμ, integral_prod_symm _ hint_a, integral_prod_symm _ (hQint γ₁ hg₁), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : ∀ x : B, Zt t (x, y) = Real.sin t • y + Real.cos t • x := fun x => by
      simp [Zt, add_comm]
    simp only [e]
    exact s11g_gaussian_ibp hg₁ hF hDF h2 (Real.sin t • y) (Real.cos t)
  have hB : ∫ q, fderiv ℝ F (Zt t q) q.2 ∂μ = Real.sin t * ∫ q, Qγ γ₂ F (Zt t q) ∂μ := by
    rw [hμ, integral_prod _ hint_b, integral_prod _ (hQint γ₂ hg₂), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e : ∀ y : B, Zt t (x, y) = Real.cos t • x + Real.sin t • y := fun y => rfl
    simp only [e]
    exact s11g_gaussian_ibp hg₂ hF hDF h2 (Real.cos t • x) (Real.sin t)
  have hsplit : ∀ q : B × B, fderiv ℝ F (Zt t q) (Zt' t q) =
      -Real.sin t * fderiv ℝ F (Zt t q) q.1 + Real.cos t * fderiv ℝ F (Zt t q) q.2 := by
    intro q
    simp only [Zt', map_add, map_smul, smul_eq_mul]
  simp_rw [hsplit]
  rw [integral_add (hint_a.const_mul _) (hint_b.const_mul _), integral_const_mul, integral_const_mul,
    hA, hB, integral_sub (hQint γ₂ hg₂) (hQint γ₁ hg₁)]
  ring

end HRS.MS.S11G
