import HRS.MS.Fp81S21DriftRS
import HRS.MS.R2InterpAux4

/-! All-real scalar measurability for projected full-history heat derivatives. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- The scalar section required by the BV selector is literally measurable for
all real times, including times outside the physical horizon. -/
theorem fp81s21_projected_heat_increment_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (P : OscPath d m H →L[ℝ] OscPath d m H)
    (Y F : Ω → ℝ → OscPath d m H)
    (hY : ∀ τ, Measurable (fun ω => Y ω τ))
    (hF : ∀ t, Measurable (fun ω => F ω t)) :
    ∀ τ a b, Measurable (fun ω =>
      fderiv ℝ (r2HeatFn γ (fun w => Ψ (P w)) τ) (Y ω τ) (F ω b - F ω a)) := by
  have hΨP : MemCb 5 (fun w => Ψ (P w)) :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof P hΨ).1
  apply fp81s21_derivative_increment_measurable
    (fun τ => r2HeatFn γ (fun w => Ψ (P w)) τ) Y F
  · intro τ
    letI := hγ τ
    exact ((s102_r2HeatFn_derivs γ τ hΨP).1).of_le (by norm_num)
  · exact fun τ => (hY τ).stronglyMeasurable
  · exact fun t => (hF t).stronglyMeasurable

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_increment_measurable
