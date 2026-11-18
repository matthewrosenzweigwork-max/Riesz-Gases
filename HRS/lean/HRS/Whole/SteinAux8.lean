import HRS.Whole.SteinAux7

/-!
# Packet STEIN, auxiliary file 8: the Hilbert-space clause of Lemma S3.7
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

section Gen

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma growth_of_bounds (F : B → ℝ) (hFd : Differentiable ℝ F) (D₁ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (x : B) : |F x| ≤ |F 0| + D₁ * ‖x‖ := by
  have h := lip_of_fderiv_bound F hFd D₁ hD₁ x 0
  rw [sub_zero, Real.norm_eq_abs] at h
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

lemma int_lin_growth_gen (Y : Ω → B) (hYm : AEStronglyMeasurable Y P)
    (hY : Integrable (fun w => ‖Y w‖) P) (F : B → ℝ) (hFc : Continuous F)
    (D₁ : ℝ) (hF : ∀ x, |F x| ≤ |F 0| + D₁ * ‖x‖) : Integrable (fun w => F (Y w)) P :=
  ((integrable_const (|F 0|)).add (hY.const_mul D₁)).mono' (hFc.comp_aestronglyMeasurable hYm)
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hF _)

end Gen

section HilbertMain

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma comp_emb_bounds {n : ℕ} (F : H → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂)
    (ι : EuclideanSpace ℝ (Fin n) →L[ℝ] H) (hι : ‖ι‖ ≤ 1) :
    ContDiff ℝ 2 (fun y => F (ι y)) ∧ (∀ y, ‖fderiv ℝ (fun y => F (ι y)) y‖ ≤ D₁) ∧
      (∀ y, ‖iteratedFDeriv ℝ 2 (fun y => F (ι y)) y‖ ≤ D₂) := by
  have hD10 : 0 ≤ D₁ := le_trans (norm_nonneg (fderiv ℝ F 0)) (hD₁ 0)
  have hD20 : 0 ≤ D₂ := le_trans (norm_nonneg (iteratedFDeriv ℝ 2 F 0)) (hD₂ 0)
  refine ⟨hF.comp ι.contDiff, fun y => ?_, fun y => ?_⟩
  · have hd : DifferentiableAt ℝ F (ι y) := (hF.differentiable (by norm_num)) _
    have e : fderiv ℝ (fun y => F (ι y)) y = (fderiv ℝ F (ι y)).comp ι := by
      have := fderiv_comp y hd ι.differentiableAt
      rw [ContinuousLinearMap.fderiv] at this
      exact this
    rw [e]
    calc ‖(fderiv ℝ F (ι y)).comp ι‖ ≤ ‖fderiv ℝ F (ι y)‖ * ‖ι‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ D₁ * 1 := mul_le_mul (hD₁ _) hι (norm_nonneg _) hD10
      _ = D₁ := mul_one _
  · have e := ι.iteratedFDeriv_comp_right (n := 2) hF y (i := 2) le_rfl
    have e' : iteratedFDeriv ℝ 2 (fun y => F (ι y)) y =
        (iteratedFDeriv ℝ 2 F (ι y)).compContinuousLinearMap fun _ => ι := e
    rw [e']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin 2, ‖ι‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) hι
    calc ‖iteratedFDeriv ℝ 2 F (ι y)‖ * ∏ _i : Fin 2, ‖ι‖ ≤ D₂ * 1 :=
          mul_le_mul (hD₂ _) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD20
      _ = D₂ := mul_one _

lemma tail_bound (e : HilbertBasis ℕ ℝ H) (n : ℕ) (Y : Ω → H) (hYm : AEStronglyMeasurable Y P)
    (hY : Integrable (fun w => ‖Y w‖) P) (F : H → ℝ) (hFd : Differentiable ℝ F) (D₁ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) :
    Integrable (fun w => F (Y w)) P ∧ Integrable (fun w => F (hproj e n (Y w))) P ∧
    |∫ w, F (Y w) ∂P - ∫ w, F (hproj e n (Y w)) ∂P| ≤ D₁ * ∫ w, ‖Y w - hproj e n (Y w)‖ ∂P := by
  have hFc : Continuous F := hFd.continuous
  have hg := growth_of_bounds F hFd D₁ hD₁
  have h1 : Integrable (fun w => F (Y w)) P := int_lin_growth_gen P Y hYm hY F hFc D₁ hg
  have hPm : AEStronglyMeasurable (fun w => hproj e n (Y w)) P :=
    (hproj_continuous e n).comp_aestronglyMeasurable hYm
  have hPn : Integrable (fun w => ‖hproj e n (Y w)‖) P :=
    hY.mono' hPm.norm (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact norm_hproj_le e n _)
  have h2 : Integrable (fun w => F (hproj e n (Y w))) P := int_lin_growth_gen P _ hPm hPn F hFc D₁ hg
  have h3 : Integrable (fun w => ‖Y w - hproj e n (Y w)‖) P :=
    (hY.add hPn).mono' (hYm.sub hPm).norm (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact norm_sub_le _ _)
  refine ⟨h1, h2, ?_⟩
  rw [← integral_sub h1 h2, ← Real.norm_eq_abs]
  have key : ‖∫ w, (F (Y w) - F (hproj e n (Y w))) ∂P‖ ≤ ∫ w, D₁ * ‖Y w - hproj e n (Y w)‖ ∂P := by
    refine norm_integral_le_of_norm_le (h3.const_mul D₁) (Eventually.of_forall fun w => ?_)
    have := lip_of_fderiv_bound F hFd D₁ hD₁ (Y w) (hproj e n (Y w))
    exact this
  rwa [integral_const_mul] at key

end HilbertMain

section HilbertFinal

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

theorem hilbert_main (e : HilbertBasis ℕ ℝ H) (X G : Ω → H) (hX : Integrable X P)
    (hG : AEMeasurable G P) (hGauss : IsCenteredGaussian (law P G)) (r τ : ℝ)
    (hfin : ∀ n : ℕ, ∃ (R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ),
      Integrable R P ∧ (∀ i j, AEStronglyMeasurable (fun w => T w i j) P) ∧
      Integrable (fun w => traceNormMatrix (T w)) P ∧
      SId P (fun w => hcoords e n (X w)) R T ∧
      ∫ w, ‖R w‖ ∂P ≤ r ∧
      ∫ w, traceNormMatrix (T w - Matrix.of fun i j : Fin n =>
        ∫ w', inner ℝ (e i) (G w') * inner ℝ (e j) (G w') ∂P) ∂P ≤ τ)
    (htailX : Tendsto (fun n => ∫ w, ‖X w - hproj e n (X w)‖ ∂P) atTop (𝓝 0))
    (htailG : Tendsto (fun n => ∫ w, ‖G w - hproj e n (G w)‖ ∂P) atTop (𝓝 0))
    (F : H → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂) :
    Integrable (fun w => F (X w)) P ∧ Integrable (fun w => F (G w)) P ∧
    |∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P| ≤ D₁ * r + (1 / 2) * D₂ * τ := by
  haveI := hilbert_secondCountable e
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G P := hG.aestronglyMeasurable
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGnorm : Integrable (fun w => ‖G w‖) P := by
    have h := gaussian_norm_integrable P G hGauss
    exact (integrable_map_measure (μ := P) (f := G) (g := fun y : H => ‖y‖)
      h.aestronglyMeasurable hG).1 h
  obtain ⟨hIX, hIXn, hXtail⟩ := tail_bound P e 0 X hXm hX.norm F hFd D₁ hD₁
  obtain ⟨hIG, hIGn, hGtail⟩ := tail_bound P e 0 G hGm hGnorm F hFd D₁ hD₁
  refine ⟨hIX, hIG, ?_⟩
  have hD10 : 0 ≤ D₁ := le_trans (norm_nonneg (fderiv ℝ F 0)) (hD₁ 0)
  have hD20 : 0 ≤ D₂ := le_trans (norm_nonneg (iteratedFDeriv ℝ 2 F 0)) (hD₂ 0)
  -- the finite-dimensional estimate for every `n`
  have hn : ∀ n : ℕ, |∫ w, F (hproj e n (X w)) ∂P - ∫ w, F (hproj e n (G w)) ∂P| ≤
      D₁ * r + (1 / 2) * D₂ * τ := by
    intro n
    obtain ⟨R, T, hR, hTm, hT, hid, hRr, hTτ⟩ := hfin n
    obtain ⟨hFc, hF1, hF2⟩ := comp_emb_bounds (n := n) F hF D₁ D₂ hD₁ hD₂ (embCLM e n) (norm_embCLM_le e n)
    have hXn : Integrable (fun w => coordCLM e n (X w)) P := (coordCLM e n).integrable_comp hX
    have hGn : AEMeasurable (fun w => coordCLM e n (G w)) P :=
      (coordCLM e n).measurable.comp_aemeasurable hG
    have hGaussn : IsCenteredGaussian (law P (fun w => coordCLM e n (G w))) := by
      have hlaw : law P (fun w => coordCLM e n (G w)) = (law P G).map (coordCLM e n) := by
        unfold law
        exact (AEMeasurable.map_map_of_aemeasurable (coordCLM e n).measurable.aemeasurable hG).symm
      rw [hlaw]
      haveI := hGauss.1
      refine ⟨ProbabilityTheory.isGaussian_map (coordCLM e n), fun L => ?_⟩
      rw [integral_map (coordCLM e n).measurable.aemeasurable L.continuous.aestronglyMeasurable]
      exact hGauss.2 (L.comp (coordCLM e n))
    have hC : ∀ i j : Fin n, (Matrix.of fun i j : Fin n =>
        ∫ w', inner ℝ (e i) (G w') * inner ℝ (e j) (G w') ∂P) i j =
        ∫ w, (coordCLM e n (G w)) i * (coordCLM e n (G w)) j ∂P := fun i j => rfl
    have key := stein_c2 P (fun w => coordCLM e n (X w)) R T hXn hR hTm hT hid
      (fun w => coordCLM e n (G w)) hGn hGaussn
      (Matrix.of fun i j : Fin n => ∫ w', inner ℝ (e i) (G w') * inner ℝ (e j) (G w') ∂P) hC
      (fun y => F (embCLM e n y)) hFc D₁ D₂ hF1 hF2
    obtain ⟨-, -, hb⟩ := key
    have e1 : ∀ w, F (embCLM e n (coordCLM e n (X w))) = F (hproj e n (X w)) := fun w => by
      rw [coordCLM_apply, embCLM_coords]
    have e2 : ∀ w, F (embCLM e n (coordCLM e n (G w))) = F (hproj e n (G w)) := fun w => by
      rw [coordCLM_apply, embCLM_coords]
    simp_rw [e1, e2] at hb
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_left hRr hD10
    have := mul_le_mul_of_nonneg_left hTτ (by positivity : (0 : ℝ) ≤ 1 / 2 * D₂)
    nlinarith
  -- pass to the limit
  have hlim : Tendsto (fun n : ℕ => D₁ * (∫ w, ‖X w - hproj e n (X w)‖ ∂P) +
      (D₁ * r + (1 / 2) * D₂ * τ) + D₁ * (∫ w, ‖G w - hproj e n (G w)‖ ∂P)) atTop
      (𝓝 (D₁ * 0 + (D₁ * r + (1 / 2) * D₂ * τ) + D₁ * 0)) :=
    ((tendsto_const_nhds.mul htailX).add tendsto_const_nhds).add (tendsto_const_nhds.mul htailG)
  have hle : ∀ n : ℕ, |∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P| ≤ D₁ * (∫ w, ‖X w - hproj e n (X w)‖ ∂P) +
      (D₁ * r + (1 / 2) * D₂ * τ) + D₁ * (∫ w, ‖G w - hproj e n (G w)‖ ∂P) := by
    intro n
    obtain ⟨hA1, hA2, hA3⟩ := tail_bound P e n X hXm hX.norm F hFd D₁ hD₁
    obtain ⟨hB1, hB2, hB3⟩ := tail_bound P e n G hGm hGnorm F hFd D₁ hD₁
    have hs := hn n
    have hsplit : ∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P =
        (∫ w, F (X w) ∂P - ∫ w, F (hproj e n (X w)) ∂P) +
        (∫ w, F (hproj e n (X w)) ∂P - ∫ w, F (hproj e n (G w)) ∂P) -
        (∫ w, F (G w) ∂P - ∫ w, F (hproj e n (G w)) ∂P) := by ring
    rw [hsplit]
    calc _ ≤ |(∫ w, F (X w) ∂P - ∫ w, F (hproj e n (X w)) ∂P) +
        (∫ w, F (hproj e n (X w)) ∂P - ∫ w, F (hproj e n (G w)) ∂P)| +
        |∫ w, F (G w) ∂P - ∫ w, F (hproj e n (G w)) ∂P| := abs_sub _ _
      _ ≤ _ := by
        have := abs_add_le (∫ w, F (X w) ∂P - ∫ w, F (hproj e n (X w)) ∂P)
          (∫ w, F (hproj e n (X w)) ∂P - ∫ w, F (hproj e n (G w)) ∂P)
        linarith
  have := ge_of_tendsto' hlim hle
  simpa using this

end HilbertFinal

end HRS.Whole.Stein
