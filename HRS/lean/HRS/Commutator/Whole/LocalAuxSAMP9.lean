import HRS.Commutator.Whole.LocalAuxSAMP8

/-!
# Pairing identities for convolutions (packet CMX-SAMP, helper file 9)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma aesm_conv_prod {κ g f : Euc d → ℂ} (hκ : AEStronglyMeasurable κ volume)
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun q : Euc d × Euc d => κ q.2 * g (q.1 - q.2) * f q.1)
      (volume.prod volume) := by
  have h1 := AEStronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hκ hg
  have h2 : AEStronglyMeasurable (fun q : Euc d × Euc d => f q.1) (volume.prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  exact (h1.mul h2).congr (Eventually.of_forall fun q => by simp)

lemma integrable_conv_growth {κ g f : Euc d → ℂ} (hκ : AEStronglyMeasurable κ volume)
    (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume)
    (hκ0 : Integrable (fun y => ‖κ y‖)) (hκ1 : Integrable (fun y => ‖y‖ * ‖κ y‖))
    {A : ℝ} (hA : 0 ≤ A) (hgA : ∀ x, ‖g x‖ ≤ A * (1 + ‖x‖))
    (hf0 : Integrable (fun x => ‖f x‖)) (hf1 : Integrable (fun x => ‖x‖ * ‖f x‖)) :
    Integrable (fun q : Euc d × Euc d => κ q.2 * g (q.1 - q.2) * f q.1) := by
  have hkb : Integrable (fun y : Euc d => ‖κ y‖ * (1 + ‖y‖)) := by
    refine (hκ0.add hκ1).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]; ring
  have hb : Integrable (fun q : Euc d × Euc d => A * (‖f q.1‖ * (‖κ q.2‖ * (1 + ‖q.2‖)) +
      ‖q.1‖ * ‖f q.1‖ * ‖κ q.2‖)) (volume.prod volume) :=
    ((hf0.mul_prod hkb).add (hf1.mul_prod hκ0)).const_mul A
  refine hb.mono' (aesm_conv_prod hκ hg hf) (Eventually.of_forall fun q => ?_)
  simp only [norm_mul]
  have h1 := hgA (q.1 - q.2)
  have h2 : ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
  have h3 : ‖g (q.1 - q.2)‖ ≤ A * (1 + (‖q.1‖ + ‖q.2‖)) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  calc ‖κ q.2‖ * ‖g (q.1 - q.2)‖ * ‖f q.1‖
      ≤ ‖κ q.2‖ * (A * (1 + (‖q.1‖ + ‖q.2‖))) * ‖f q.1‖ := by gcongr
    _ = _ := by ring

lemma integrable_conv_holder {κ g f : Euc d → ℂ} (hκ : AEStronglyMeasurable κ volume)
    (hκ0 : Integrable κ) (hg : AEStronglyMeasurable g volume) (hf : AEStronglyMeasurable f volume)
    {P P' : ℝ≥0∞} [P.HolderConjugate P'] (hgP : MemLp g P volume) (hfP : MemLp f P' volume) :
    Integrable (fun q : Euc d × Euc d => κ q.2 * g (q.1 - q.2) * f q.1) := by
  have hmeas := aesm_conv_prod hκ hg hf
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hm2 := hmeas.enorm
  refine lt_of_eq_of_lt (lintegral_prod_symm _ hm2) ?_
  have hfin : eLpNorm g P volume * eLpNorm f P' volume < ⊤ :=
    ENNReal.mul_lt_top hgP.eLpNorm_lt_top hfP.eLpNorm_lt_top
  calc ∫⁻ y, ∫⁻ x, ‖κ (x, y).2 * g ((x, y).1 - (x, y).2) * f (x, y).1‖ₑ
      ≤ ∫⁻ y, ‖κ y‖ₑ * (eLpNorm g P volume * eLpNorm f P' volume) := by
        refine lintegral_mono fun y => ?_
        have h : ∀ x : Euc d, ‖κ (x, y).2 * g ((x, y).1 - (x, y).2) * f (x, y).1‖ₑ
            = ‖κ y‖ₑ * ‖g (x - y) * f x‖ₑ := by
          intro x
          simp only
          rw [mul_assoc, enorm_mul]
        simp_rw [h]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        gcongr
        have := lintegral_holder_shift hgP hfP (-y)
        simpa [sub_eq_add_neg] using this
    _ = (∫⁻ y, ‖κ y‖ₑ) * (eLpNorm g P volume * eLpNorm f P' volume) :=
        lintegral_mul_const' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top hκ0.2 hfin

/-- `∫ (κ * g) f = ∫ g (κ ⋆ f)` with `(κ ⋆ f)(x) = ∫ κ(y) f(x+y) dy`. -/
lemma pairing_conv (κ g f : Euc d → ℂ)
    (h1 : Integrable (fun q : Euc d × Euc d => κ q.2 * g (q.1 - q.2) * f q.1)) :
    Integrable (fun x => (∫ y, κ y * g (x - y)) * f x) ∧
    Integrable (fun x => g x * ∫ y, κ y * f (x + y)) ∧
    ∫ x, (∫ y, κ y * g (x - y)) * f x = ∫ x, g x * ∫ y, κ y * f (x + y) := by
  have h2 : Integrable (fun q : Euc d × Euc d => κ q.2 * g q.1 * f (q.1 + q.2))
      (volume.prod volume) := by
    have := (measurePreserving_add_prod (volume : Measure (Euc d)) (volume : Measure (Euc d))
      ).integrable_comp_of_integrable h1
    refine this.congr (Eventually.of_forall fun q => ?_)
    simp
  refine ⟨?_, ?_, ?_⟩
  · have := h1.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const]
  · have := h2.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  · rw [integral_conv_mul_swap κ g f h1]
    have e1 : ∀ y : Euc d, ∫ x, g (x - y) * f x = ∫ x, g x * f (x + y) := by
      intro y
      rw [← integral_add_right_eq_self (fun x : Euc d => g (x - y) * f x) y]
      simp
    simp_rw [e1]
    have e2 : ∀ y : Euc d, κ y * ∫ x, g x * f (x + y) = ∫ x, κ y * g x * f (x + y) := by
      intro y; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    simp_rw [e2]
    rw [integral_integral_swap (f := fun y x => κ y * g x * f (x + y)) h2.swap]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)

end HRS.Commutator.Whole.SAMP1
