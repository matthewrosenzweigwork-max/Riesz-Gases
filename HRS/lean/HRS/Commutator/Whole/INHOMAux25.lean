import HRS.Commutator.Whole.INHOMAux24

/-!
# CMX-INHOM auxiliary 25: `L²` continuity of the commutator form (`(4.L2-continuity)`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_amgm {t : ℝ} (ht : 0 < t) (u w : ℝ) :
    2 * (|u| * |w|) ≤ t * u ^ 2 + t⁻¹ * w ^ 2 := by
  have e : t * (|u| - t⁻¹ * |w|) ^ 2 = t * |u| ^ 2 - 2 * (|u| * |w|) + t⁻¹ * |w| ^ 2 := by
    field_simp; ring
  have h := mul_nonneg ht.le (sq_nonneg (|u| - t⁻¹ * |w|))
  rw [e, sq_abs, sq_abs] at h
  linarith

/-- Schur test for a symmetric non-negative `L¹` kernel. -/
lemma inhom_schur {W : Euc d → ℝ} (hWm : Measurable W) (hW : Integrable W volume)
    (hWn : ∀ z, 0 ≤ W z) (hWe : ∀ z, W (-z) = W z) {f g : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ 2) volume) (hg2 : Integrable (fun x => g x ^ 2) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : Euc d × Euc d => W (p.1 - p.2) * (|f p.1| * |g p.2|))
        (volume.prod volume) ∧
      ∫ p : Euc d × Euc d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ∂(volume.prod volume) ≤
        (t * (∫ x, f x ^ 2) + t⁻¹ * (∫ x, g x ^ 2)) / 2 * ∫ z, W z := by
  have hA := inhom_int_shear' hf2 hW hWe
  have hB := inhom_int_shear hg2 hW
  have hbound : ∀ p : Euc d × Euc d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ≤
      (t / 2) * (f p.1 ^ 2 * W (p.1 - p.2)) + (t⁻¹ / 2) * (g p.2 ^ 2 * W (p.1 - p.2)) := by
    intro p
    have h := inhom_amgm ht (f p.1) (g p.2)
    have hw := hWn (p.1 - p.2)
    nlinarith [mul_le_mul_of_nonneg_left h hw]
  have hmeasf : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.1) (volume.prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeasg : AEStronglyMeasurable (fun p : Euc d × Euc d => g p.2) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hWd : Measurable fun p : Euc d × Euc d => W (p.1 - p.2) :=
    hWm.comp (measurable_fst.sub measurable_snd)
  have hint : Integrable (fun p : Euc d × Euc d => W (p.1 - p.2) * (|f p.1| * |g p.2|))
      (volume.prod volume) := by
    refine (((hA.const_mul (t / 2)).add (hB.const_mul (t⁻¹ / 2)))).mono'
      (hWd.aestronglyMeasurable.mul (hmeasf.norm.mul hmeasg.norm)) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hWn _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    exact hbound p
  refine ⟨hint, ?_⟩
  have hI1 : ∫ p : Euc d × Euc d, f p.1 ^ 2 * W (p.1 - p.2) ∂(volume.prod volume) =
      (∫ x, f x ^ 2) * ∫ z, W z := by
    rw [integral_prod _ hA]
    have : ∀ x : Euc d, ∫ y : Euc d, f x ^ 2 * W (x - y) = f x ^ 2 * ∫ z, W z := by
      intro x
      rw [integral_const_mul, integral_sub_left_eq_self W volume x]
    simp_rw [this]
    rw [integral_mul_const]
  have hI2 : ∫ p : Euc d × Euc d, g p.2 ^ 2 * W (p.1 - p.2) ∂(volume.prod volume) =
      (∫ x, g x ^ 2) * ∫ z, W z := by
    rw [integral_prod_symm _ hB]
    have : ∀ y : Euc d, ∫ x : Euc d, g y ^ 2 * W (x - y) = g y ^ 2 * ∫ z, W z := by
      intro y
      rw [integral_const_mul, integral_sub_right_eq_self W y]
    simp_rw [this]
    rw [integral_mul_const]
  calc ∫ p : Euc d × Euc d, W (p.1 - p.2) * (|f p.1| * |g p.2|) ∂(volume.prod volume)
      ≤ ∫ p : Euc d × Euc d, ((t / 2) * (f p.1 ^ 2 * W (p.1 - p.2)) +
          (t⁻¹ / 2) * (g p.2 ^ 2 * W (p.1 - p.2))) ∂(volume.prod volume) :=
        integral_mono hint ((hA.const_mul (t / 2)).add (hB.const_mul (t⁻¹ / 2))) hbound
    _ = (t / 2) * ((∫ x, f x ^ 2) * ∫ z, W z) + (t⁻¹ / 2) * ((∫ x, g x ^ 2) * ∫ z, W z) := by
        rw [integral_add (hA.const_mul (t / 2)) (hB.const_mul (t⁻¹ / 2)), integral_const_mul,
          integral_const_mul, hI1, hI2]
    _ = _ := by ring

end HRS.Commutator.Whole
