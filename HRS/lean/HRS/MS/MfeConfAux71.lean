import HRS.MS.MfeConfAux70

/-!
# S.B.1, packet F8 (part 3): convolution toolkit, derivative, Lipschitz bound, integration by parts
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_cv_hasFDerivAt {f φ : Euc d → ℝ} {A L : ℝ} (hf : Sb1Gr f A) (hfd : Differentiable ℝ f)
    (hfc : Continuous (fderiv ℝ f)) (hL : ∀ z, ‖fderiv ℝ f z‖ ≤ L) (hm : AEStronglyMeasurable φ volume)
    (h1 : Integrable φ) (h2 : Integrable (fun y => |φ y| * ‖y‖)) (x : Euc d) :
    HasFDerivAt (sb1_lv_cv f φ) (∫ y, φ y • fderiv ℝ f (x - y)) x := by
  have hLm : ∀ x', AEStronglyMeasurable (fun y => φ y • fderiv ℝ f (x' - y)) volume := fun x' =>
    hm.smul (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbd : ∀ x' y, ‖φ y • fderiv ℝ f (x' - y)‖ ≤ L * |φ y| := by
    intro x' y
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left (hL (x' - y)) (abs_nonneg (φ y))
    linarith [mul_comm L |φ y|]
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (F := fun x y => φ y * f (x - y)) (F' := fun x y => φ y • fderiv ℝ f (x - y)) (x₀ := x)
    (s := Set.univ) (bound := fun y => L * |φ y|) Filter.univ_mem
    (Eventually.of_forall fun x' => hm.mul (hf.1.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (sb1_lv_cv_int hf hm h1 h2 x) (hLm x) (Eventually.of_forall fun y x' _ => hbd x' y)
    (h1.abs.const_mul L) ?_
  · exact this
  · refine Eventually.of_forall fun y x' _ => ?_
    have h1 : HasFDerivAt (fun x' => f (x' - y)) (fderiv ℝ f (x' - y)) x' :=
      (hfd (x' - y)).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const y)
    exact (h1.const_mul (φ y)).congr_fderiv (by ext v; simp)

theorem sb1_lv_cv_lip {f φ : Euc d → ℝ} {A L : ℝ} (hf : Sb1Gr f A) (hlip : ∀ z z', |f z - f z'| ≤ L * ‖z - z'‖)
    (hm : AEStronglyMeasurable φ volume) (h1 : Integrable φ) (h2 : Integrable (fun y => |φ y| * ‖y‖))
    (x x' : Euc d) :
    |sb1_lv_cv f φ x - sb1_lv_cv f φ x'| ≤ L * ‖x - x'‖ * ∫ y, |φ y| := by
  unfold sb1_lv_cv
  rw [← integral_sub (sb1_lv_cv_int hf hm h1 h2 x) (sb1_lv_cv_int hf hm h1 h2 x')]
  have hpt : ∀ y, ‖φ y * f (x - y) - φ y * f (x' - y)‖ ≤ L * ‖x - x'‖ * |φ y| := fun y => by
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h := hlip (x - y) (x' - y)
    have e : x - y - (x' - y) = x - x' := by abel
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h (abs_nonneg (φ y))
    linarith [mul_comm (L * ‖x - x'‖) |φ y|]
  have := norm_integral_le_of_norm_le (h1.abs.const_mul (L * ‖x - x'‖)) (Eventually.of_forall hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at this
  exact this

/-- Integration by parts: `∫ ρ(y) (D κ)(x-y) v dy = ∫ (Dρ)(y) v κ(x-y) dy`. -/
theorem sb1_lv_ibp_cv {κ ρ : Euc d → ℝ} (hκd : Differentiable ℝ κ) (hκc : Continuous (fderiv ℝ κ)) {L Ak : ℝ}
    (hL : ∀ z, ‖fderiv ℝ κ z‖ ≤ L) (hAk : ∀ z, |κ z| ≤ Ak) (hρd : Differentiable ℝ ρ)
    (hρc : Continuous ρ) (hρ' : Continuous (fderiv ℝ ρ)) (hρi : Integrable ρ)
    (v : Euc d) (hρ'i : Integrable (fun y => fderiv ℝ ρ y v)) (x : Euc d) :
    ∫ y, ρ y * fderiv ℝ κ (x - y) v = ∫ y, fderiv ℝ ρ y v * κ (x - y) := by
  have hκm : Continuous (fun y => κ (x - y)) := hκd.continuous.comp (continuous_const.sub continuous_id)
  have i1 : Integrable (fun y => fderiv ℝ ρ y v * κ (x - y)) := by
    refine (hρ'i.norm.mul_const Ak).mono' (hρ'i.aestronglyMeasurable.mul hκm.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hAk _) (norm_nonneg _)
  have hgd : ∀ y, fderiv ℝ (fun y => κ (x - y)) y v = -(fderiv ℝ κ (x - y) v) := by
    intro y
    have h1 : HasFDerivAt (fun y => κ (x - y)) ((fderiv ℝ κ (x - y)).comp (-ContinuousLinearMap.id ℝ (Euc d))) y :=
      (hκd (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    rw [h1.fderiv]
    simp
  have i2 : Integrable (fun y => ρ y * fderiv ℝ (fun y => κ (x - y)) y v) := by
    have : Integrable (fun y => ρ y * fderiv ℝ κ (x - y) v) := by
      refine (hρi.norm.mul_const (L * ‖v‖)).mono' (hρc.aestronglyMeasurable.mul
        (((hκc.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))
    refine this.neg.congr (Eventually.of_forall fun y => ?_)
    simp only [hgd, mul_neg, Pi.neg_apply]
  have i3 : Integrable (fun y => ρ y * κ (x - y)) := by
    refine (hρi.norm.mul_const Ak).mono' (hρc.aestronglyMeasurable.mul hκm.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hAk _) (norm_nonneg _)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := ρ) (g := fun y => κ (x - y)) (v := v) i1 i2 i3 (fun y _ => hρd y)
    (fun y _ => (hκd.comp (differentiable_const x |>.sub differentiable_id)) y)
  simp only [hgd, mul_neg, integral_neg, neg_inj] at key
  exact key

end HRS.MS.MfeConf
