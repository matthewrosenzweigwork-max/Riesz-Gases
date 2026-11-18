import HRS.MS.Fp81S21DriftRS3

/-! Projection-independent bound for the heat-gradient operator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- The projected heat gradient is bounded independently of the projection,
its evaluation point and the heat parameter. -/
theorem fp81s21_projected_heat_gradient_norm_le
    {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (P : OscPath d m H →L[ℝ] OscPath d m H) (hP : ‖P‖ ≤ 1)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (τ : ℝ) (y : OscPath d m H) :
    ‖fderiv ℝ (r2HeatFn γ (fun w => Ψ (P w)) τ) y‖ ≤ cbNorm 5 Ψ := by
  let A : OscPath d m H →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (OscPath d m H) ℝ
      (s102_projHeatD γ Ψ P 1 τ y)
  have hA : ‖A‖ ≤ cbNorm 5 Ψ := by
    letI := hγ τ
    dsimp only [A]
    rw [LinearIsometryEquiv.norm_map]
    unfold s102_projHeatD
    have hb : ‖∫ z, iteratedFDeriv ℝ 1 Ψ (P (y + z)) ∂(γ τ)‖ ≤
        cbNorm 5 Ψ * (γ τ).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z =>
        HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΨ (by norm_num) _)
    simpa using hb
  have heq : fderiv ℝ (r2HeatFn γ (fun w => Ψ (P w)) τ) y = A.comp P := by
    ext v
    have h := s102_proj_deriv γ hγ P hΨ 1 (by norm_num) τ y (fun _ => v)
    rw [iteratedFDeriv_one_apply] at h
    have hv : (fun _ : Fin 1 => P v) = ![P v] := by
      ext i
      fin_cases i
      rfl
    rw [hv] at h
    simpa [A, continuousMultilinearCurryFin1_apply] using h
  rw [heq]
  calc
    ‖A.comp P‖ ≤ ‖A‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le A P
    _ ≤ cbNorm 5 Ψ * 1 := mul_le_mul hA hP (norm_nonneg _) (by
      exact HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΨ 0)
    _ = cbNorm 5 Ψ := mul_one _

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_gradient_norm_le
