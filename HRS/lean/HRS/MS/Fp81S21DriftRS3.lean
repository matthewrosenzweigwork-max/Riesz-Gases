import HRS.MS.Fp81S21DriftRS2

/-! Operator-norm continuity for projected heat gradients. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Along a continuous prediction path, a projected heat gradient is continuous
in operator norm on the whole horizon. -/
theorem fp81s21_projected_heat_gradient_continuousOn
    {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hP : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (L : ℕ) (Y : ℝ → OscPath d m H) (hY : ContinuousOn Y (Icc 0 H)) :
    ContinuousOn (fun τ => fderiv ℝ
      (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y τ)) (Icc 0 H) := by
  have hΨP : MemCb 5 (fun w => Ψ (Pj L w)) :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Pj L) hΨ).1
  have hc := (s102_conv_equicont γ hγ Pj hP hconv hLP hΨP Y hY 1 (by norm_num)).1
  have hc' := (continuousMultilinearCurryFin1 ℝ (OscPath d m H) ℝ).continuous.comp_continuousOn hc
  change ContinuousOn (fun τ => continuousMultilinearCurryFin1 ℝ (OscPath d m H) ℝ
    (iteratedFDeriv ℝ 1 (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y τ))) (Icc 0 H) at hc'
  simpa only [s102_curry_iter] using hc'

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_gradient_continuousOn
