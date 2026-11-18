import HRS.MS.FldRemCen4

/-! Time Cauchy–Schwarz and Tonelli with an almost-everywhere energy bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21

theorem fp81s21_g4_integrated_cs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {v w : ℝ} {B : ℝ≥0∞}
    {h : Ω → ℝ → ℝ≥0∞} (hm : Measurable (fun z : Ω × ℝ => h z.1 z.2))
    (hB : ∀ᵐ q ∂(volume.restrict (Icc v w)), ∫⁻ z, h z q ^ 2 ∂μ ≤ B) :
    (∫⁻ z, (∫⁻ q in Icc v w, h z q) ^ 2 ∂μ) ≤
      ENNReal.ofReal (w - v) * (ENNReal.ofReal (w - v) * B) := by
  have hcs : ∀ z, (∫⁻ q in Icc v w, h z q) ^ 2 ≤
      ENNReal.ofReal (w - v) * ∫⁻ q in Icc v w, h z q ^ 2 := by
    intro z
    have hq : Measurable (fun q => h z q) := hm.comp (measurable_const.prodMk measurable_id)
    have ht := HRS.MS.S53.s53_cs_sq (volume.restrict (Icc v w)) hq.aemeasurable
    rwa [Measure.restrict_apply_univ, Real.volume_Icc] at ht
  have hs : Measurable (fun z : Ω × ℝ => h z.1 z.2 ^ 2) := hm.pow_const 2
  calc
    _ ≤ ∫⁻ z, (ENNReal.ofReal (w - v) * ∫⁻ q in Icc v w, h z q ^ 2) ∂μ :=
      lintegral_mono hcs
    _ = ENNReal.ofReal (w - v) * ∫⁻ q in Icc v w, ∫⁻ z, h z q ^ 2 ∂μ := by
      rw [lintegral_const_mul _ (hs.lintegral_prod_right'), lintegral_lintegral_swap hs.aemeasurable]
    _ ≤ ENNReal.ofReal (w - v) * ∫⁻ _q in Icc v w, B :=
      mul_le_mul_right (lintegral_mono_ae hB) _
    _ = _ := by rw [setLIntegral_const, Real.volume_Icc, mul_comm B]

#print axioms fp81s21_g4_integrated_cs
end HRS.Fp81.S21
end
