import HRS.Commutator.Whole.INHOMAux6

/-!
# CMX-INHOM auxiliary 7: the pairing identity for bounded and for `L¹` odd kernels
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_int_shear {f g : Euc d → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun p : Euc d × Euc d => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
  have := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  simpa using this

lemma inhom_int_shear' {f g : Euc d → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hgn : ∀ z, g (-z) = g z) :
    Integrable (fun p : Euc d × Euc d => f p.1 * g (p.1 - p.2)) (volume.prod volume) := by
  have := (inhom_int_shear hf hg).swap
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
  rw [← hgn (p.2 - p.1), neg_sub]

lemma inhom_ghi_odd {s : ℝ} (z : Euc d) : ghiForce s (-z) = -ghiForce s z := by
  unfold ghiForce
  rw [cmxFB_kernGrad_neg, cmxFB_gloForce_neg, neg_sub_neg, neg_sub]

lemma inhom_ghi_measurable (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Measurable (ghiForce s : Euc d → Euc d) :=
  (cmxSA_kernGrad_measurable s).sub (cmxMY_gloForce_continuous hd hs0 hsd).measurable

theorem inhom_pairing_L1 {H V : Euc d → Euc d} {a : Euc d → ℝ} (hHm : Measurable H)
    (hodd : ∀ x, H (-x) = -H x) (hH1 : Integrable (fun z => ‖H z‖) volume)
    (hVc : Continuous V) {C : ℝ} (hVg : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖))
    (hac : Continuous a) (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume)
    {M : ℝ} (hM : ∀ x, |a x| ≤ M) :
    CcommFun H V a = 2 * ∫ x, a x * inner ℝ (V x) (inhom_conv H a x) := by
  have hC : 0 ≤ C := by
    have := hVg 0; simp at this; exact (norm_nonneg _).trans this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hgn : ∀ z, ‖H (-z)‖ = ‖H z‖ := fun z => by rw [hodd, norm_neg]
  have hmeas : ∀ (u w : Euc d × Euc d → Euc d), Measurable u → Measurable w →
      Measurable (fun p : Euc d × Euc d => inner ℝ (u p) (w p) * a p.1 * a p.2) := by
    intro u w hu hw
    exact ((hu.inner hw).mul (hac.measurable.comp measurable_fst)).mul
      (hac.measurable.comp measurable_snd)
  have hHd : Measurable fun p : Euc d × Euc d => H (p.1 - p.2) :=
    hHm.comp (measurable_fst.sub measurable_snd)
  refine inhom_pairing hodd ?_ ?_ ?_
  · refine ((inhom_int_shear' hai hH1 hgn).const_mul (M * C)).mono'
      (hmeas (fun p => V p.1) _ (hVc.measurable.comp measurable_fst) hHd).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |inner ℝ (V p.1) (H (p.1 - p.2))| ≤ C * (1 + ‖p.1‖) * ‖H (p.1 - p.2)‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hVg _) (norm_nonneg _))
    calc |inner ℝ (V p.1) (H (p.1 - p.2))| * |a p.1| * |a p.2|
        ≤ (C * (1 + ‖p.1‖) * ‖H (p.1 - p.2)‖) * |a p.1| * M := by
          gcongr
          exact hM _
      _ = M * C * (((1 + ‖p.1‖) * |a p.1|) * ‖H (p.1 - p.2)‖) := by ring
  · refine ((inhom_int_shear hai hH1).const_mul (M * C)).mono'
      (hmeas (fun p => V p.2) _ (hVc.measurable.comp measurable_snd) hHd).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |inner ℝ (V p.2) (H (p.1 - p.2))| ≤ C * (1 + ‖p.2‖) * ‖H (p.1 - p.2)‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hVg _) (norm_nonneg _))
    calc |inner ℝ (V p.2) (H (p.1 - p.2))| * |a p.1| * |a p.2|
        ≤ (C * (1 + ‖p.2‖) * ‖H (p.1 - p.2)‖) * M * |a p.2| := by
          gcongr
          exact hM _
      _ = M * C * (((1 + ‖p.2‖) * |a p.2|) * ‖H (p.1 - p.2)‖) := by ring
  · intro x
    refine ((hH1.comp_sub_left x).const_mul M).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (hac.measurable.smul (hHm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

theorem inhom_pairing_bdd {H V : Euc d → Euc d} {a : Euc d → ℝ} (hHm : Measurable H)
    (hodd : ∀ x, H (-x) = -H x) {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B)
    (hVc : Continuous V) {C : ℝ} (hVg : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖))
    (hac : Continuous a) (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume) :
    CcommFun H V a = 2 * ∫ x, a x * inner ℝ (V x) (inhom_conv H a x) := by
  have hC : 0 ≤ C := by
    have := hVg 0; simp at this; exact (norm_nonneg _).trans this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨ha1, -⟩ := lowv_a_int_aux hac hai
  have hmeas : ∀ (u w : Euc d × Euc d → Euc d), Measurable u → Measurable w →
      Measurable (fun p : Euc d × Euc d => inner ℝ (u p) (w p) * a p.1 * a p.2) := by
    intro u w hu hw
    exact ((hu.inner hw).mul (hac.measurable.comp measurable_fst)).mul
      (hac.measurable.comp measurable_snd)
  have hHd : Measurable fun p : Euc d × Euc d => H (p.1 - p.2) :=
    hHm.comp (measurable_fst.sub measurable_snd)
  refine inhom_pairing hodd ?_ ?_ ?_
  · refine (((hai.mul_prod ha1)).const_mul (B * C)).mono'
      (hmeas (fun p => V p.1) _ (hVc.measurable.comp measurable_fst) hHd).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |inner ℝ (V p.1) (H (p.1 - p.2))| ≤ C * (1 + ‖p.1‖) * B :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hVg _) (hB _) (norm_nonneg _) (by positivity))
    calc |inner ℝ (V p.1) (H (p.1 - p.2))| * |a p.1| * |a p.2|
        ≤ (C * (1 + ‖p.1‖) * B) * |a p.1| * |a p.2| := by gcongr
      _ = B * C * (((1 + ‖p.1‖) * |a p.1|) * |a p.2|) := by ring
  · refine (((ha1.mul_prod hai)).const_mul (B * C)).mono'
      (hmeas (fun p => V p.2) _ (hVc.measurable.comp measurable_snd) hHd).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |inner ℝ (V p.2) (H (p.1 - p.2))| ≤ C * (1 + ‖p.2‖) * B :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hVg _) (hB _) (norm_nonneg _) (by positivity))
    calc |inner ℝ (V p.2) (H (p.1 - p.2))| * |a p.1| * |a p.2|
        ≤ (C * (1 + ‖p.2‖) * B) * |a p.1| * |a p.2| := by gcongr
      _ = B * C * (|a p.1| * ((1 + ‖p.2‖) * |a p.2|)) := by ring
  · intro x
    refine (ha1.const_mul B).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (hac.measurable.smul (hHm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs]
      calc |a y| * ‖H (x - y)‖ ≤ |a y| * B := mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
        _ = B * |a y| := by ring

end HRS.Commutator.Whole
