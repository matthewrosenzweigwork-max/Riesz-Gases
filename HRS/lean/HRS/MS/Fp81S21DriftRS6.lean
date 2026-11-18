import HRS.MS.Fp81S21DriftRS5

/-! The pathwise continuity and variation hypotheses for the BV selector. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Continuous prediction paths and bounded-variation cumulatives supply the
selector's pathwise hypotheses simultaneously for every valid subinterval. -/
theorem fp81s21_projected_heat_bv_good
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {m H : ℝ}
    (μ : Measure Ω) (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hP : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y F : Ω → ℝ → OscPath d m H)
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (Y ω) (Icc 0 H))
    (hF : ∀ᵐ ω ∂μ, BoundedVariationOn (F ω) (Icc 0 H)) :
    ∀ᵐ ω ∂μ, ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      ContinuousOn (fun τ => fderiv ℝ
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ)) (Icc q r) ∧
      BoundedVariationOn (F ω) (Icc q r) := by
  filter_upwards [hY, hF] with ω hy hf
  intro L q r hq hqr hr
  have hs : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
  exact ⟨(fp81s21_projected_heat_gradient_continuousOn γ hγ Pj hP hconv hLP
    Ψ hΨ L (Y ω) hy).mono hs, hf.mono hs⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_bv_good
