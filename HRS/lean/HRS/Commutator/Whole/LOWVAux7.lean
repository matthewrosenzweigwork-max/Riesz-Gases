import HRS.Commutator.Whole.LOWVAux6

/-!
# CMX-LOWV auxiliary 7: integrability and bounds for `𝒞_F(V,a)` with `a` Schwartz-like
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

theorem lowv_a_int_aux {a : Euc d → ℝ} (hac : Continuous a)
    (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|)) :
    Integrable (fun y : Euc d => |a y|) ∧ Integrable (fun y : Euc d => ‖y‖ * |a y|) := by
  refine ⟨?_, ?_⟩
  · refine hai.mono' hac.abs.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have : 0 ≤ |a y| := abs_nonneg _
    nlinarith [norm_nonneg y]
  · refine hai.mono' ((continuous_norm.mul hac.abs).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : 0 ≤ |a y| := abs_nonneg _
    nlinarith [norm_nonneg y]

theorem lowv_glo_piece {F V : Euc d → Euc d} {Lv B : ℝ} (hFc : Continuous F)
    (hB : ∀ x, ‖F x‖ ≤ B) (hVc : Continuous V) (hV : ∀ x y, ‖V x - V y‖ ≤ Lv * ‖x - y‖)
    (hLv : 0 ≤ Lv) {a : Euc d → ℝ} (hac : Continuous a)
    (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|)) :
    Integrable (fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume) := by
  obtain ⟨ha1, ha2⟩ := lowv_a_int_aux hac hai
  have hKc := lowv_K_continuous hFc hVc
  have hKb := lowv_K_bound hB hV hLv
  have hg : Integrable (fun p : Euc d × Euc d => (Lv * B) * ((‖p.1‖ * |a p.1|) * |a p.2|) +
      (Lv * B) * (|a p.1| * (‖p.2‖ * |a p.2|))) (volume.prod volume) :=
    (((ha2.mul_prod ha1)).const_mul _).add ((ha1.mul_prod ha2).const_mul _)
  refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2 := by
      simp_rw [lowv_commKer_eq]
      exact (hKc.mul (hac.comp continuous_fst)).mul (hac.comp continuous_snd)
    exact this.aestronglyMeasurable
  · rw [lowv_commKer_eq, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |lowv_K F V p.1 p.2| * |a p.1| * |a p.2|
        ≤ ((Lv * B) * (‖p.1‖ + ‖p.2‖)) * |a p.1| * |a p.2| := by
          gcongr; exact hKb _ _
      _ = _ := by ring

theorem lowv_ghi_piece {F V : Euc d → Euc d} {Lv : ℝ} (hFm : Measurable F) (hVc : Continuous V)
    (hV : ∀ x y, ‖V x - V y‖ ≤ Lv * ‖x - y‖) (hLv : 0 ≤ Lv)
    (hk : Integrable (fun z : Euc d => ‖z‖ * ‖F z‖)) {a : Euc d → ℝ} (hac : Continuous a)
    {M : ℝ} (hM : ∀ x, |a x| ≤ M) (ha1 : Integrable (fun y : Euc d => |a y|))
    (ha2 : Integrable (fun x : Euc d => a x ^ 2)) :
    Integrable (fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume) ∧
    |CcommFun F V a| ≤ Lv * (∫ z, ‖z‖ * ‖F z‖) * ∫ x, a x ^ 2 := by
  set k : Euc d → ℝ := fun z => ‖z‖ * ‖F z‖ with hkdef
  have hk0 : ∀ z, 0 ≤ k z := fun z => by positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hpt : ∀ x y : Euc d, |commKer F V x y| ≤ Lv * k (x - y) := by
    intro x y
    rw [lowv_commKer_eq]
    unfold lowv_K
    calc |inner ℝ (V x - V y) (F (x - y))| ≤ ‖V x - V y‖ * ‖F (x - y)‖ := abs_real_inner_le_norm _ _
      _ ≤ (Lv * ‖x - y‖) * ‖F (x - y)‖ := by gcongr; exact hV x y
      _ = Lv * k (x - y) := by simp only [hkdef]; ring
  have hKm : Measurable fun p : Euc d × Euc d => commKer F V p.1 p.2 := by
    have e : (fun p : Euc d × Euc d => commKer F V p.1 p.2) =
        fun p => lowv_K F V p.1 p.2 := funext fun p => lowv_commKer_eq F V p.1 p.2
    rw [e]
    unfold lowv_K
    exact ((hVc.measurable.comp measurable_fst).sub (hVc.measurable.comp measurable_snd)).inner
      (hFm.comp (measurable_fst.sub measurable_snd))
  have hfm : AEStronglyMeasurable (fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume) :=
    ((hKm.mul (hac.measurable.comp measurable_fst)).mul
      (hac.measurable.comp measurable_snd)).aestronglyMeasurable
  have hconv := Integrable.convolution_integrand (μ := (volume : Measure (Euc d)))
    (ν := (volume : Measure (Euc d))) (ContinuousLinearMap.mul ℝ ℝ) ha1 hk
  -- the two pieces
  have hP2 : Integrable (fun p : Euc d × Euc d => k (p.1 - p.2) * a p.2 ^ 2) (volume.prod volume) := by
    have := Integrable.convolution_integrand (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d))) (ContinuousLinearMap.mul ℝ ℝ) ha2 hk
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    ring
  have hP1 : Integrable (fun p : Euc d × Euc d => k (p.1 - p.2) * a p.1 ^ 2) (volume.prod volume) := by
    have hk' : Integrable (fun z : Euc d => k (-z)) := hk.comp_neg
    have := (Integrable.convolution_integrand (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d))) (ContinuousLinearMap.mul ℝ ℝ) ha2 hk').swap
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, ContinuousLinearMap.mul_apply']
    rw [show -(p.2 - p.1) = p.1 - p.2 by abel]
    ring
  have hint : Integrable (fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume) := by
    refine (hconv.const_mul (Lv * M)).mono' hfm (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [ContinuousLinearMap.mul_apply']
    calc |commKer F V p.1 p.2| * |a p.1| * |a p.2| ≤ (Lv * k (p.1 - p.2)) * M * |a p.2| := by
          gcongr
          · exact hpt _ _
          · exact hM _
      _ = Lv * M * (|a p.2| * k (p.1 - p.2)) := by ring
  refine ⟨hint, ?_⟩
  have hCC : CcommFun F V a = ∫ p : Euc d × Euc d, commKer F V p.1 p.2 * a p.1 * a p.2
      ∂(volume.prod volume) := by
    unfold CcommFun
    rw [integral_prod _ hint]
  have hN : ∀ x : Euc d, ∫ y, k (x - y) = ∫ z, k z := fun x =>
    integral_sub_left_eq_self k volume x
  have hN' : ∀ y : Euc d, ∫ x, k (x - y) = ∫ z, k z := fun y =>
    integral_sub_right_eq_self k y
  have hI1 : ∫ p : Euc d × Euc d, k (p.1 - p.2) * a p.1 ^ 2 ∂(volume.prod volume) =
      (∫ z, k z) * ∫ x, a x ^ 2 := by
    rw [integral_prod _ hP1]
    have : ∀ x : Euc d, ∫ y, k (x - y) * a x ^ 2 = (∫ z, k z) * a x ^ 2 := fun x => by
      rw [integral_mul_const, hN x]
    simp_rw [this]
    rw [integral_const_mul]
  have hI2 : ∫ p : Euc d × Euc d, k (p.1 - p.2) * a p.2 ^ 2 ∂(volume.prod volume) =
      (∫ z, k z) * ∫ x, a x ^ 2 := by
    rw [integral_prod _ hP2]
    have hs := integral_integral_swap (f := fun x y : Euc d => k (x - y) * a y ^ 2) hP2
    rw [hs]
    have : ∀ y : Euc d, ∫ x, k (x - y) * a y ^ 2 = (∫ z, k z) * a y ^ 2 := fun y => by
      rw [integral_mul_const, hN' y]
    simp_rw [this]
    rw [integral_const_mul]
  have hg2 : Integrable (fun p : Euc d × Euc d => (Lv / 2) * (k (p.1 - p.2) * a p.1 ^ 2 +
      k (p.1 - p.2) * a p.2 ^ 2)) (volume.prod volume) := (hP1.add hP2).const_mul _
  have hle : ∫ p : Euc d × Euc d, ‖commKer F V p.1 p.2 * a p.1 * a p.2‖ ∂(volume.prod volume) ≤
      ∫ p : Euc d × Euc d, (Lv / 2) * (k (p.1 - p.2) * a p.1 ^ 2 + k (p.1 - p.2) * a p.2 ^ 2)
        ∂(volume.prod volume) := by
    refine integral_mono hint.norm hg2 fun p => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |commKer F V p.1 p.2| ≤ Lv * k (p.1 - p.2) := hpt _ _
    have h2 : |a p.1| * |a p.2| ≤ (a p.1 ^ 2 + a p.2 ^ 2) / 2 := by
      nlinarith [sq_abs (a p.1), sq_abs (a p.2), sq_nonneg (|a p.1| - |a p.2|)]
    calc |commKer F V p.1 p.2| * |a p.1| * |a p.2|
        = |commKer F V p.1 p.2| * (|a p.1| * |a p.2|) := by ring
      _ ≤ (Lv * k (p.1 - p.2)) * ((a p.1 ^ 2 + a p.2 ^ 2) / 2) := by
          gcongr
      _ = _ := by ring
  rw [hCC]
  calc |∫ p : Euc d × Euc d, commKer F V p.1 p.2 * a p.1 * a p.2 ∂(volume.prod volume)|
      = ‖∫ p : Euc d × Euc d, commKer F V p.1 p.2 * a p.1 * a p.2 ∂(volume.prod volume)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ p : Euc d × Euc d, ‖commKer F V p.1 p.2 * a p.1 * a p.2‖ ∂(volume.prod volume) :=
        norm_integral_le_integral_norm _
    _ ≤ _ := hle
    _ = Lv * (∫ z, k z) * ∫ x, a x ^ 2 := by
        rw [integral_const_mul, integral_add hP1 hP2, hI1, hI2]
        ring

end HRS.Commutator.Whole
