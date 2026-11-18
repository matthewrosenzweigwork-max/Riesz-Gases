import HRS.MS.Fp81S21DriftRS5

/-! Uniform pathwise domination of the exact BV variation majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- On every ordered subinterval the exact RS majorant is dominated by the
full-horizon variation times a test-dependent constant, independently of the
projection and the prediction. This does not assert majorant measurability. -/
theorem fp81s21_projected_heat_variation_majorant_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (P : OscPath d m H →L[ℝ] OscPath d m H) (hP : ‖P‖ ≤ 1)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y F : Ω → ℝ → OscPath d m H) (ω : Ω) (V : ℝ)
    (hBV : BoundedVariationOn (F ω) (Icc 0 H))
    (hV : (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V)
    {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H) :
    fp81s21_rs_bv_variation_majorant
      (fun ω τ => fderiv ℝ (r2HeatFn γ (fun w => Ψ (P w)) τ) (Y ω τ))
      F q r ω ≤ cbNorm 5 Ψ * V := by
  letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
  have hs : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
  have hv : (eVariationOn (F ω) (Icc q r)).toReal ≤ V :=
    (ENNReal.toReal_mono hBV (eVariationOn.mono (F ω) hs)).trans hV
  have hsup : (⨆ τ : Icc q r, ‖fderiv ℝ
      (r2HeatFn γ (fun w => Ψ (P w)) τ) (Y ω τ)‖) ≤ cbNorm 5 Ψ := by
    apply ciSup_le
    intro τ
    exact fp81s21_projected_heat_gradient_norm_le γ hγ P hP Ψ hΨ τ (Y ω τ)
  unfold fp81s21_rs_bv_variation_majorant
  calc
    _ ≤ cbNorm 5 Ψ * (eVariationOn (F ω) (Icc q r)).toReal :=
      mul_le_mul_of_nonneg_right hsup ENNReal.toReal_nonneg
    _ ≤ cbNorm 5 Ψ * V := mul_le_mul_of_nonneg_left hv
      (HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΨ 0)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_variation_majorant_le
