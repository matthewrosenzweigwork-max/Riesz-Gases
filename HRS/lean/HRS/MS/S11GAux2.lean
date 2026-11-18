import HRS.Prob.Gaussian

/-!
# S11G: Gaussian integration by parts with linearly growing gradient

Variant of `HRS.gaussian_ibp` where `‖DΦ w‖ ≤ M1 + M2 ‖w‖` replaces the boundedness of `DΦ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS ProbabilityTheory

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {γ : Measure B} [IsProbabilityMeasure γ]

theorem s11g_gaussian_ibp (hγ : IsCenteredGaussian γ) {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {M1 M2 : ℝ} (h1 : ∀ w, ‖fderiv ℝ Φ w‖ ≤ M1 + M2 * ‖w‖) (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2)
    (c : B) (s : ℝ) :
    ∫ w, fderiv ℝ Φ (c + s • w) w ∂γ =
      s * ∫ w, ∫ z, fderiv ℝ (fderiv ℝ Φ) (c + s • w) z z ∂γ ∂γ := by
  have := hγ.1
  have hM1 : 0 ≤ M1 := by
    have := h1 0
    simp only [norm_zero, mul_zero, add_zero] at this
    exact (norm_nonneg _).trans this
  have hM2 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) 0)).trans (h2 0)
  have hd1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
  have hd2 : Continuous (fderiv ℝ (fderiv ℝ Φ)) := by
    have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
    exact this.continuous_fderiv (by norm_num)
  have hdiff1 : Differentiable ℝ (fderiv ℝ Φ) := by
    have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
    exact this.differentiable (by norm_num)
  set μ := γ.prod γ with hμ
  have hint1 : Integrable (fun w : B => ‖w‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hint2 := HRS.gaussian_sqnorm_integrable hγ
  -- the rotated integrand
  let pt : ℝ → B × B → B := fun θ q => c + s • (Real.cos θ • q.1 + Real.sin θ • q.2)
  let vec : ℝ → B × B → B := fun θ q => -(Real.sin θ) • q.1 + Real.cos θ • q.2
  let F : ℝ → B × B → ℝ := fun θ q => fderiv ℝ Φ (pt θ q) (vec θ q)
  let F' : ℝ → B × B → ℝ := fun θ q =>
    fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q) (vec θ q) +
      fderiv ℝ Φ (pt θ q) (-(Real.cos θ • q.1 + Real.sin θ • q.2))
  have hFcont : ∀ θ, Continuous (F θ) := fun θ => by
    simp only [F, pt, vec]
    exact hd1.comp (by fun_prop) |>.clm_apply (by fun_prop)
  -- invariance
  have hrotmeas : ∀ θ : ℝ, Measurable (ContinuousLinearMap.rotation θ : B × B → B × B) :=
    fun θ => (ContinuousLinearMap.rotation θ).continuous.measurable
  have hJ : ∀ θ, ∫ q, F θ q ∂μ = ∫ q, F 0 q ∂μ := by
    intro θ
    have hrot := IsGaussian.map_rotation_eq_self (μ := γ) (HRS.gaussian_integral_id_eq_zero hγ) θ
    have e : ∀ q : B × B, F θ q = F 0 (ContinuousLinearMap.rotation θ q) := by
      intro q
      simp [F, pt, vec, ContinuousLinearMap.rotation_apply]
    have h := integral_map (μ := μ) (hrotmeas θ).aemeasurable (f := F 0)
      (hFcont 0).aestronglyMeasurable
    rw [hrot] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall e)
  -- pointwise derivative
  have hpt : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => pt θ q) (s • vec θ q) θ := by
    intro θ q
    have h1 := ((Real.hasDerivAt_cos θ).smul_const q.1).add ((Real.hasDerivAt_sin θ).smul_const q.2)
    have h2 := (h1.const_smul s).const_add c
    convert h2 using 1
  have hvec : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => vec θ q)
      (-(Real.cos θ • q.1 + Real.sin θ • q.2)) θ := by
    intro θ q
    have h1 := ((Real.hasDerivAt_sin θ).neg.smul_const q.1).add ((Real.hasDerivAt_cos θ).smul_const q.2)
    convert h1 using 1
    module
  have hderivF : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => F θ q) (F' θ q) θ := by
    intro θ q
    have h1 : HasDerivAt (fun θ => fderiv ℝ Φ (pt θ q))
        (fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)) θ :=
      (hdiff1 (pt θ q)).hasFDerivAt.comp_hasDerivAt θ (hpt θ q)
    exact h1.clm_apply (hvec θ q)
  have hn1 : ∀ (θ : ℝ) (q : B × B), ‖vec θ q‖ ≤ ‖q.1‖ + ‖q.2‖ := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, norm_neg, Real.norm_eq_abs]
    have a1 := Real.abs_sin_le_one θ
    have a2 := Real.abs_cos_le_one θ
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  have hn2 : ∀ (θ : ℝ) (q : B × B), ‖Real.cos θ • q.1 + Real.sin θ • q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs]
    have a1 := Real.abs_sin_le_one θ
    have a2 := Real.abs_cos_le_one θ
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  have hnpt : ∀ (θ : ℝ) (q : B × B), ‖pt θ q‖ ≤ ‖c‖ + |s| * (‖q.1‖ + ‖q.2‖) := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hn2 θ q) (abs_nonneg _))
  have hDF : ∀ (w v : B), ‖fderiv ℝ Φ w v‖ ≤ (M1 + M2 * ‖w‖) * ‖v‖ := fun w v =>
    ((fderiv ℝ Φ w).le_opNorm v).trans (mul_le_mul_of_nonneg_right (h1 w) (norm_nonneg v))
  have hDFpt : ∀ (θ : ℝ) (q : B × B) (v : B), ‖v‖ ≤ ‖q.1‖ + ‖q.2‖ →
      ‖fderiv ℝ Φ (pt θ q) v‖ ≤ (M1 + M2 * ‖c‖) * (‖q.1‖ + ‖q.2‖) +
        M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 := by
    intro θ q v hv
    have h0 : 0 ≤ ‖q.1‖ + ‖q.2‖ := by positivity
    calc ‖fderiv ℝ Φ (pt θ q) v‖ ≤ (M1 + M2 * ‖pt θ q‖) * ‖v‖ := hDF _ _
      _ ≤ (M1 + M2 * (‖c‖ + |s| * (‖q.1‖ + ‖q.2‖))) * (‖q.1‖ + ‖q.2‖) := by
          refine mul_le_mul ?_ hv (norm_nonneg _) ?_
          · linarith [mul_le_mul_of_nonneg_left (hnpt θ q) hM2]
          · have : 0 ≤ ‖c‖ + |s| * (‖q.1‖ + ‖q.2‖) := by positivity
            nlinarith [mul_nonneg hM2 this]
      _ = _ := by ring
  set bF : B × B → ℝ := fun q => (M1 + M2 * ‖c‖) * (‖q.1‖ + ‖q.2‖) +
    M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 with hbF
  set b : B × B → ℝ := fun q => M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 + bF q with hb
  have hn1int : Integrable (fun q : B × B => ‖q.1‖ + ‖q.2‖) μ :=
    (hint1.comp_fst γ).add (hint1.comp_snd γ)
  have hn2int : Integrable (fun q : B × B => (‖q.1‖ + ‖q.2‖) ^ 2) μ := by
    have := ((hint2.comp_fst γ).add ((hint1.mul_prod hint1).const_mul 2)).add (hint2.comp_snd γ)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    ring
  have hbFint : Integrable bF μ := (hn1int.const_mul _).add (hn2int.const_mul _)
  have hbint : Integrable b μ := (hn2int.const_mul _).add hbFint
  have hFbound : ∀ (θ : ℝ) (q : B × B), ‖F θ q‖ ≤ bF q := by
    intro θ q
    exact hDFpt θ q _ (hn1 θ q)
  have hF'bound : ∀ (θ : ℝ) (q : B × B), ‖F' θ q‖ ≤ b q := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q) (vec θ q)‖ ≤
        M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 := by
      refine ((fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)).le_opNorm _).trans ?_
      have : ‖fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)‖ ≤ M2 * (|s| * (‖q.1‖ + ‖q.2‖)) := by
        refine ((fderiv ℝ (fderiv ℝ Φ) (pt θ q)).le_opNorm _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (h2 _) (mul_le_mul_of_nonneg_left (hn1 θ q) (abs_nonneg _)) (by positivity) hM2
      calc _ ≤ M2 * (|s| * (‖q.1‖ + ‖q.2‖)) * (‖q.1‖ + ‖q.2‖) :=
            mul_le_mul this (hn1 θ q) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have e2 : ‖fderiv ℝ Φ (pt θ q) (-(Real.cos θ • q.1 + Real.sin θ • q.2))‖ ≤ bF q := by
      refine hDFpt θ q _ ?_
      rw [norm_neg]
      exact hn2 θ q
    exact add_le_add e1 e2
  have hF'cont : ∀ θ, Continuous (F' θ) := fun θ => by
    simp only [F', pt, vec]
    refine Continuous.add ?_ ?_
    · exact (hd2.comp (by fun_prop)).clm_apply (by fun_prop) |>.clm_apply (by fun_prop)
    · exact (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := 0) (bound := b) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun θ => (hFcont θ).aestronglyMeasurable)
    (hbFint.mono' (hFcont 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hFbound 0 q))
    (hF'cont 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q θ _ => hF'bound θ q) hbint
    (Filter.Eventually.of_forall fun q θ _ => hderivF θ q)
  have hconst : HasDerivAt (fun θ => ∫ q, F θ q ∂μ) 0 0 := by
    have : (fun θ => ∫ q, F θ q ∂μ) = fun _ => ∫ q, F 0 q ∂μ := funext hJ
    rw [this]; exact hasDerivAt_const _ _
  have hzero : ∫ q, F' 0 q ∂μ = 0 := hD.2.unique hconst
  -- evaluate at θ = 0
  have hF'0 : ∀ q : B × B, F' 0 q = s * fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 -
      fderiv ℝ Φ (c + s • q.1) q.1 := by
    intro q
    simp [F', pt, vec]
    ring
  have hAcont : Continuous fun q : B × B => fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 :=
    ((hd2.comp (by fun_prop)).clm_apply (by fun_prop)).clm_apply (by fun_prop)
  have hBcont : Continuous fun q : B × B => fderiv ℝ Φ (c + s • q.1) q.1 :=
    (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  have hAint : Integrable (fun q : B × B => fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2) μ := by
    refine (hint2.comp_snd γ |>.const_mul M2).mono' hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    refine ((fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2).le_opNorm _).trans ?_
    have : ‖fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2‖ ≤ M2 * ‖q.2‖ :=
      ((fderiv ℝ (fderiv ℝ Φ) (c + s • q.1)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (h2 _) (norm_nonneg _))
    calc _ ≤ M2 * ‖q.2‖ * ‖q.2‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  set gB : B → ℝ := fun w => (M1 + M2 * ‖c‖) * ‖w‖ + M2 * |s| * ‖w‖ ^ 2 with hgB
  have hDFB : ∀ w : B, ‖fderiv ℝ Φ (c + s • w) w‖ ≤ gB w := by
    intro w
    refine (hDF _ _).trans ?_
    have : ‖c + s • w‖ ≤ ‖c‖ + |s| * ‖w‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
    calc (M1 + M2 * ‖c + s • w‖) * ‖w‖ ≤ (M1 + M2 * (‖c‖ + |s| * ‖w‖)) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left this hM2]) (norm_nonneg _)
      _ = gB w := by simp only [hgB]; ring
  have hgBint : Integrable gB γ := (hint1.const_mul _).add (hint2.const_mul _)
  have hBint : Integrable (fun q : B × B => fderiv ℝ Φ (c + s • q.1) q.1) μ := by
    refine (hgBint.comp_fst γ).mono' hBcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hDFB q.1)
  have hBint' : Integrable (fun w : B => fderiv ℝ Φ (c + s • w) w) γ := by
    refine hgBint.mono' ?_ (Filter.Eventually.of_forall fun w => hDFB w)
    exact ((hd1.comp (by fun_prop : Continuous fun w : B => c + s • w)).clm_apply
        continuous_id).aestronglyMeasurable
  have hz : s * ∫ q, fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 ∂μ -
      ∫ q, fderiv ℝ Φ (c + s • q.1) q.1 ∂μ = 0 := by
    rw [← integral_const_mul, ← integral_sub (hAint.const_mul s) hBint]
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hF'0 q).symm)
  rw [integral_prod _ hAint] at hz
  have hB := HRS.integral_fst_prod (γ := γ) (g := fun w => fderiv ℝ Φ (c + s • w) w) hBint'
  linarith



end HRS.MS.S11G
