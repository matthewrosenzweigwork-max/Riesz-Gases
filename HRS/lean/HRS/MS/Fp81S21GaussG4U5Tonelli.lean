import HRS.MS.FldRemCen4

/-! Conversion of an iterated real energy bound to a product-measure bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21

theorem fp81s21_g4_energy_tonelli {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {q B : ℝ}
    {F : ℝ × X → ℝ} (hF : Measurable F) (hF0 : ∀ z, 0 ≤ F z)
    (hFx : ∀ r ∈ Icc (0 : ℝ) q, Integrable (fun x => F (r, x)) μ)
    (hFr : IntegrableOn (fun r => ∫ x, F (r, x) ∂μ) (Icc (0 : ℝ) q))
    (hB : (∫ r in Icc (0 : ℝ) q, ∫ x, F (r, x) ∂μ) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (F z) ∂((volume.restrict (Icc (0 : ℝ) q)).prod μ)) ≤
      ENNReal.ofReal B := by
  have hslice : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) q)),
      (∫⁻ x, ENNReal.ofReal (F (r, x)) ∂μ) =
        ENNReal.ofReal (∫ x, F (r, x) ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (ofReal_integral_eq_lintegral_ofReal (hFx r hr)
      (Filter.Eventually.of_forall fun x => hF0 (r, x))).symm
  calc
    _ = ∫⁻ r in Icc (0 : ℝ) q, ∫⁻ x, ENNReal.ofReal (F (r, x)) ∂μ :=
      lintegral_prod _ (ENNReal.measurable_ofReal.comp hF).aemeasurable
    _ = ∫⁻ r in Icc (0 : ℝ) q, ENNReal.ofReal (∫ x, F (r, x) ∂μ) :=
      lintegral_congr_ae hslice
    _ = ENNReal.ofReal (∫ r in Icc (0 : ℝ) q, ∫ x, F (r, x) ∂μ) := by
      exact (ofReal_integral_eq_lintegral_ofReal hFr
        (Filter.Eventually.of_forall fun r => integral_nonneg fun x => hF0 (r, x))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hB

#print axioms fp81s21_g4_energy_tonelli
end HRS.Fp81.S21
end
