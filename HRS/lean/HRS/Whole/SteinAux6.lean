import HRS.Whole.SteinAux5

/-!
# Packet STEIN, auxiliary file 6: from `C_b^5` to `C²` test functions
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {n : ℕ}

theorem stein_cb5 (X R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SId P X R T)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΦ : MemCb 5 Φ) (a b : ℝ)
    (ha : ∀ x, ‖fderiv ℝ Φ x‖ ≤ a) (hb : ∀ x, ‖iteratedFDeriv ℝ 2 Φ x‖ ≤ b) :
    |∫ w, Φ (X w) ∂P - ∫ w, Φ (G w) ∂P| ≤
      a * ∫ w, ‖R w‖ ∂P + (1 / 2) * b * ∫ w, traceNormMatrix (T w - C) ∂P := by
  obtain ⟨-, hu5, hub⟩ := stein_bounds P G hG hGauss Φ hΦ
  have heq := stein_equation P G hG hGauss Φ hΦ
  obtain ⟨K, hK⟩ := hΦ.2 0 (Nat.zero_le _)
  have hΦK : ∀ x, |Φ x| ≤ K := by
    intro x
    have := hK ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have hne : Nonempty (EuclideanSpace ℝ (Fin n)) := ⟨0⟩
  have h1 : ∀ x, ‖fderiv ℝ (steinSolution P G Φ) x‖ ≤ a := by
    intro x
    have := hub 1 le_rfl (by norm_num) x
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans ?_
    have hs : (⨆ y, ‖iteratedFDeriv ℝ 1 Φ y‖) ≤ a :=
      ciSup_le fun y => by rw [norm_iteratedFDeriv_one]; exact ha y
    simpa using hs
  have h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ (steinSolution P G Φ)) x‖ ≤ (1 / 2) * b := by
    intro x
    have e : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (steinSolution P G Φ)) x‖ =
        ‖iteratedFDeriv ℝ 2 (steinSolution P G Φ) x‖ := norm_iteratedFDeriv_fderiv (n := 1)
    rw [norm_iteratedFDeriv_one] at e
    rw [e]
    refine (hub 2 (by norm_num) (by norm_num) x).trans ?_
    have hs : (⨆ y, ‖iteratedFDeriv ℝ 2 Φ y‖) ≤ b := ciSup_le fun y => hb y
    have : ((2 : ℕ) : ℝ)⁻¹ * (⨆ y, ‖iteratedFDeriv ℝ 2 Φ y‖) ≤ ((2 : ℕ) : ℝ)⁻¹ * b :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    simpa using this
  have h3 : ∀ x, ‖iteratedFDeriv ℝ 3 (steinSolution P G Φ) x‖ ≤
      ((3 : ℕ) : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ 3 Φ y‖ := fun x =>
    hub 3 (by norm_num) (by norm_num) x
  have key := stein_core_u P X R T hX hR hTm hT hid G hG hGauss C hC Φ hΦ.1.continuous K hΦK
    (steinSolution P G Φ) hu5 a ((1 / 2) * b) h1 h2 _ h3 heq
  calc _ ≤ _ := key
    _ = _ := by ring

theorem stein_trunc (X R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SId P X R T)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂)
    (ρ : ℝ) (hρ : 0 < ρ) :
    |∫ w, atr ρ (F (X w)) ∂P - ∫ w, atr ρ (F (G w)) ∂P| ≤
      D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * (D₂ + D₁ ^ 2 / ρ) * ∫ w, traceNormMatrix (T w - C) ∂P := by
  obtain ⟨hFRc, hFRb, hFR1, hFR2⟩ := trunc_props F hF D₁ D₂ hD₁ hD₂ ρ hρ
  set FR : EuclideanSpace ℝ (Fin n) → ℝ := fun x => atr ρ (F x) with hFRdef
  have hFRcont : Continuous FR := hFRc.continuous
  set M : ℝ := ρ * (Real.pi / 2) with hM
  set b : ℝ := D₂ + D₁ ^ 2 / ρ with hb
  have hD10 : 0 ≤ D₁ := le_trans (norm_nonneg (fderiv ℝ F 0)) (hD₁ 0)
  have hD20 : 0 ≤ D₂ := le_trans (norm_nonneg (iteratedFDeriv ℝ 2 F 0)) (hD₂ 0)
  have hbnn : 0 ≤ b := by positivity
  have hDi : ∀ j, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j FR x‖ ≤ (if j = 1 then D₁ else b) := by
    intro j h1 hj x
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · simpa [norm_iteratedFDeriv_one] using hFR1 x
    · simpa using hFR2 x
  have hmd := fun k => mol_deriv (bumpSeq n k) FR 2 (by norm_num) hFRc M hFRb
    (fun j => if j = 1 then D₁ else b) hDi
  have hmem : ∀ k, MemCb 5 (mol ((bumpSeq n k).normed volume) FR) := by
    intro k
    refine ⟨?_, fun j hj => ?_⟩
    · exact_mod_cast (mol_smooth (bumpSeq n k) FR hFRcont M hFRb 5).1
    · obtain ⟨K, hK⟩ := (mol_smooth (bumpSeq n k) FR hFRcont M hFRb 5).2 j hj
      exact ⟨K, by rintro _ ⟨x, rfl⟩; exact hK x⟩
  have hbd : ∀ k x, |mol ((bumpSeq n k).normed volume) FR x| ≤ M := fun k x =>
    mol_abs_le (bumpSeq n k) FR M hFRb x
  have hk : ∀ k, |∫ w, mol ((bumpSeq n k).normed volume) FR (X w) ∂P -
      ∫ w, mol ((bumpSeq n k).normed volume) FR (G w) ∂P| ≤
      D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * b * ∫ w, traceNormMatrix (T w - C) ∂P := by
    intro k
    refine stein_cb5 P X R T hX hR hTm hT hid G hG hGauss C hC _ (hmem k) D₁ b ?_ ?_
    · intro x
      have := (hmd k).2.2 1 le_rfl (by norm_num) x
      simpa [norm_iteratedFDeriv_one] using this
    · intro x
      simpa using (hmd k).2.2 2 (by norm_num) le_rfl x
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G P := hG.aestronglyMeasurable
  have hlimX : Tendsto (fun k => ∫ w, mol ((bumpSeq n k).normed volume) FR (X w) ∂P) atTop
      (𝓝 (∫ w, FR (X w) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
      (integrable_const _) (fun k => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => mol_tendsto (bumpSeq n) (bumpSeq_rOut_tendsto n) FR hFRcont (X w))
    · exact (hmem k).1.continuous.comp_aestronglyMeasurable hXm
    · rw [Real.norm_eq_abs]; exact hbd k _
  have hlimG : Tendsto (fun k => ∫ w, mol ((bumpSeq n k).normed volume) FR (G w) ∂P) atTop
      (𝓝 (∫ w, FR (G w) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
      (integrable_const _) (fun k => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => mol_tendsto (bumpSeq n) (bumpSeq_rOut_tendsto n) FR hFRcont (G w))
    · exact (hmem k).1.continuous.comp_aestronglyMeasurable hGm
    · rw [Real.norm_eq_abs]; exact hbd k _
  exact le_of_tendsto' (hlimX.sub hlimG).abs hk

lemma gauss_norm_integrable' (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) : Integrable (fun w => ‖G w‖) P := by
  have h := gaussian_norm_integrable P G hGauss
  exact (integrable_map_measure (μ := P) (f := G) (g := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖)
    h.aestronglyMeasurable hG).1 h

lemma int_lin_growth (Y : Ω → EuclideanSpace ℝ (Fin n)) (hYm : AEStronglyMeasurable Y P)
    (hY : Integrable (fun w => ‖Y w‖) P) (F : EuclideanSpace ℝ (Fin n) → ℝ) (hFc : Continuous F)
    (D₁ : ℝ) (hF : ∀ x, |F x| ≤ |F 0| + D₁ * ‖x‖) : Integrable (fun w => F (Y w)) P :=
  ((integrable_const (|F 0|)).add (hY.const_mul D₁)).mono' (hFc.comp_aestronglyMeasurable hYm)
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hF _)

theorem stein_c2 (X R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SId P X R T)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂) :
    Integrable (fun w => F (X w)) P ∧ Integrable (fun w => F (G w)) P ∧
    |∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P| ≤
      D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * D₂ * ∫ w, traceNormMatrix (T w - C) ∂P := by
  have hFc : Continuous F := hF.continuous
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hgrow : ∀ x, |F x| ≤ |F 0| + D₁ * ‖x‖ := by
    intro x
    have h := lip_of_fderiv_bound F hFd D₁ hD₁ x 0
    rw [sub_zero, Real.norm_eq_abs] at h
    have := abs_sub_abs_le_abs_sub (F x) (F 0)
    linarith
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G P := hG.aestronglyMeasurable
  have hIX : Integrable (fun w => F (X w)) P := int_lin_growth P X hXm hX.norm F hFc D₁ hgrow
  have hIG : Integrable (fun w => F (G w)) P :=
    int_lin_growth P G hGm (gauss_norm_integrable' P G hG hGauss) F hFc D₁ hgrow
  refine ⟨hIX, hIG, ?_⟩
  have hD10 : 0 ≤ D₁ := le_trans (norm_nonneg (fderiv ℝ F 0)) (hD₁ 0)
  have hD20 : 0 ≤ D₂ := le_trans (norm_nonneg (iteratedFDeriv ℝ 2 F 0)) (hD₂ 0)
  have hbound : ∀ᶠ ρ : ℝ in atTop,
      |∫ w, atr ρ (F (X w)) ∂P - ∫ w, atr ρ (F (G w)) ∂P| ≤
        D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * (D₂ + D₁ ^ 2 / ρ) * ∫ w, traceNormMatrix (T w - C) ∂P := by
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    exact stein_trunc P X R T hX hR hTm hT hid G hG hGauss C hC F hF D₁ D₂ hD₁ hD₂ ρ hρ
  have hlimX : Tendsto (fun ρ : ℝ => ∫ w, atr ρ (F (X w)) ∂P) atTop (𝓝 (∫ w, F (X w) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => |F (X w)|)
      (Eventually.of_forall fun ρ => ?_) ?_ hIX.abs (Eventually.of_forall fun w => atr_tendsto _)
    · exact ((atr_contDiff ρ (m := 0)).continuous.comp hFc).comp_aestronglyMeasurable hXm
    · filter_upwards [eventually_gt_atTop 0] with ρ hρ
      exact Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact abs_atr_le _ _ hρ
  have hlimG : Tendsto (fun ρ : ℝ => ∫ w, atr ρ (F (G w)) ∂P) atTop (𝓝 (∫ w, F (G w) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => |F (G w)|)
      (Eventually.of_forall fun ρ => ?_) ?_ hIG.abs (Eventually.of_forall fun w => atr_tendsto _)
    · exact ((atr_contDiff ρ (m := 0)).continuous.comp hFc).comp_aestronglyMeasurable hGm
    · filter_upwards [eventually_gt_atTop 0] with ρ hρ
      exact Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact abs_atr_le _ _ hρ
  have hq : Tendsto (fun ρ : ℝ => D₁ ^ 2 / ρ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hrhs : Tendsto (fun ρ : ℝ => D₁ * ∫ w, ‖R w‖ ∂P +
      (1 / 2) * (D₂ + D₁ ^ 2 / ρ) * ∫ w, traceNormMatrix (T w - C) ∂P) atTop
      (𝓝 (D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * (D₂ + 0) * ∫ w, traceNormMatrix (T w - C) ∂P)) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.mul (tendsto_const_nhds.add hq)).mul tendsto_const_nhds)
  have := le_of_tendsto_of_tendsto (hlimX.sub hlimG).abs hrhs hbound
  simpa using this

end HRS.Whole.Stein
