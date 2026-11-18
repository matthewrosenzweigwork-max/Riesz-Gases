import HRS.Commutator.Whole.INHOMAux17

/-!
# CMX-INHOM auxiliary 18: closeness of `P_{≤L}f` to `f` for Lipschitz `f`; Hölder bounds
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_Pleq_close {L' : ℝ} (hL' : 0 < L') :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : Euc d → ℝ) (Λ : ℝ), 0 ≤ Λ → (∀ x y, |f x - f y| ≤ Λ * ‖x - y‖) →
      ∀ x, |f x - Pleq L' f x| ≤ M * Λ := by
  have hG := lowv_psiL_integrable_mul (d := d) hL' 1
  refine ⟨∫ y : Euc d, (1 + ‖y‖) ^ 1 * |psiL L' y|, integral_nonneg fun y => by positivity,
    fun f Λ hΛ hf x => ?_⟩
  have hfc : Continuous f := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    refine Metric.continuousAt_iff.2 fun ε hε => ?_
    refine ⟨ε / (Λ + 1), by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy
    rw [Real.dist_eq]
    calc |f y - f z| ≤ Λ * ‖y - z‖ := hf y z
      _ ≤ (Λ + 1) * ‖y - z‖ := by gcongr; linarith
      _ < (Λ + 1) * (ε / (Λ + 1)) := by gcongr
      _ = ε := by field_simp
  have habs : Integrable (fun y : Euc d => |psiL L' y|) volume := by
    simpa using lowv_psiL_integrable_mul (d := d) hL' 0
  have hψ1 : Integrable (psiL L' : Euc d → ℝ) volume :=
    (integrable_norm_iff (lowv_psiL_continuous hL').aestronglyMeasurable).1
      (by simpa [Real.norm_eq_abs] using habs)
  have hfx : Integrable (fun y => psiL L' y * f (x - y)) volume := by
    refine (hG.const_mul (|f x| + Λ)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((lowv_psiL_continuous hL').mul (hfc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |f (x - y)| ≤ |f x| + Λ * ‖y‖ := by
        have := hf (x - y) x
        rw [sub_sub_cancel_left, norm_neg] at this
        calc |f (x - y)| = |f x + (f (x - y) - f x)| := by ring_nf
          _ ≤ |f x| + |f (x - y) - f x| := abs_add_le _ _
          _ ≤ |f x| + Λ * ‖y‖ := by gcongr
      calc |psiL L' y| * |f (x - y)| ≤ |psiL L' y| * ((|f x| + Λ) * (1 + ‖y‖)) := by
            gcongr
            nlinarith [norm_nonneg y, abs_nonneg (f x), mul_nonneg hΛ (norm_nonneg y)]
        _ = (|f x| + Λ) * ((1 + ‖y‖) ^ 1 * |psiL L' y|) := by ring
  have hint1 : ∫ y : Euc d, psiL L' y = 1 := cmxFB_integral_psiL hL'
  have e1 : f x - Pleq L' f x = ∫ y, psiL L' y * (f x - f (x - y)) := by
    unfold Pleq
    simp only [smul_eq_mul]
    have h2 : ∫ y : Euc d, psiL L' y * f x = f x := by
      rw [integral_mul_const, hint1, one_mul]
    have h3 : ∫ y, psiL L' y * (f x - f (x - y)) =
        (∫ y : Euc d, psiL L' y * f x) - ∫ y : Euc d, psiL L' y * f (x - y) := by
      rw [← integral_sub (hψ1.mul_const _) hfx]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      ring
    rw [h3, h2]
  rw [e1]
  have hb : Integrable (fun y : Euc d => Λ * ((1 + ‖y‖) ^ 1 * |psiL L' y|)) volume := hG.const_mul Λ
  calc |∫ y, psiL L' y * (f x - f (x - y))|
      = ‖∫ y, psiL L' y * (f x - f (x - y))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, Λ * ((1 + ‖y‖) ^ 1 * |psiL L' y|) := by
        refine norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have := hf x (x - y)
        rw [sub_sub_cancel] at this
        calc |psiL L' y| * |f x - f (x - y)| ≤ |psiL L' y| * (Λ * ‖y‖) := by gcongr
          _ ≤ |psiL L' y| * (Λ * (1 + ‖y‖)) := by gcongr; linarith
          _ = Λ * ((1 + ‖y‖) ^ 1 * |psiL L' y|) := by ring
    _ = (∫ y : Euc d, (1 + ‖y‖) ^ 1 * |psiL L' y|) * Λ := by
        rw [integral_const_mul, mul_comm]

lemma inhom_holder12 {f g : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    ENNReal.ofReal |∫ x, f x * g x| ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h1 : ENNReal.ofReal |∫ x, f x * g x| ≤ ∫⁻ x, ‖f x * g x‖ₑ := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  refine h1.trans ?_
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf hg
  have hm : AEStronglyMeasurable (f • g) volume := hf.smul hg
  rw [eLpNorm_one_eq_lintegral_enorm hm] at h2
  exact h2

lemma inhom_holder_triple {P Q : ℝ≥0∞} [ENNReal.HolderTriple P Q 2] {f g : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => f x * g x) 2 volume ≤ eLpNorm f P volume * eLpNorm g Q volume := by
  exact eLpNorm_smul_le_mul_eLpNorm (p := P) (q := Q) (r := 2) hf hg

lemma inhom_bdd_mul {f q : Euc d → ℝ} (hf : AEStronglyMeasurable f volume) (hq : AEStronglyMeasurable q volume)
    {M : ℝ} (hM : ∀ x, |q x| ≤ M) :
    eLpNorm (fun x => f x * q x) 2 volume ≤ ENNReal.ofReal M * eLpNorm f 2 volume := by
  have hm : AEStronglyMeasurable (fun x => f x * q x) volume := hf.mul hq
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (Eventually.of_forall fun x => ?_) 2
  show ‖f x * q x‖ ≤ M * ‖f x‖
  rw [norm_mul, Real.norm_eq_abs, mul_comm]
  gcongr
  exact hM x

end HRS.Commutator.Whole
