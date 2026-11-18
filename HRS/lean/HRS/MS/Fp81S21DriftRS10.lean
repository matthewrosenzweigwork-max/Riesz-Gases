import HRS.MS.Fp81S21DriftRS6
import HRS.MS.Fp81S21DriftRS7
import HRS.MS.Fp81S21DriftRS9

/-! Specified projected-heat BV families with a common integrable bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Measurable continuous prediction and BV cumulative paths give one scalar
RS family at each projection level. The exact majorant is integrable and is
bounded by a single integrable function selected before the projection level. -/
theorem fp81s21_projected_heat_rsbv_window
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {m H : ℝ}
    (μ : Measure Ω) (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hP : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y F : Ω → ℝ → OscPath d m H) (V : Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Y ω t))
    (hFm : ∀ t, Measurable (fun ω => F ω t))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (Y ω) (Icc 0 H))
    (hFc : ∀ᵐ ω ∂μ, ContinuousOn (F ω) (Icc 0 H))
    (hVint : Integrable V μ)
    (hV : ∀ᵐ ω ∂μ, BoundedVariationOn (F ω) (Icc 0 H) ∧
      (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V ω) :
    let Ad := fun L ω τ => fderiv ℝ
      (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ)
    ∃ M : Ω → ℝ, Integrable M μ ∧ ∀ L,
      Nonempty (fp81s21_RSBVWindow μ H (Ad L) F) ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        Integrable (fp81s21_rs_bv_variation_majorant (Ad L) F q r) μ ∧
        ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
  let Ad := fun L ω τ => fderiv ℝ
    (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ)
  let M : Ω → ℝ := fun ω => cbNorm 5 Ψ * V ω
  have hMint : Integrable M μ := hVint.const_mul _
  have hgood := fp81s21_projected_heat_bv_good μ γ hγ Pj hP hconv hLP Ψ hΨ Y F hYc
    (hV.mono fun _ h => h.1)
  have hsection : ∀ L τ, Measurable (fun ω => ‖Ad L ω τ‖) := by
    intro L τ
    have hΨP : MemCb 5 (fun w => Ψ (Pj L w)) :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Pj L) hΨ).1
    letI := hγ τ
    have hdiff : ContDiff ℝ 1 (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) :=
      ((s102_r2HeatFn_derivs γ τ hΨP).1).of_le (by norm_num)
    have hc : Continuous (fderiv ℝ (r2HeatFn γ (fun w => Ψ (Pj L w)) τ)) :=
      hdiff.continuous_fderiv (by norm_num)
    exact (hc.comp_stronglyMeasurable (hYm τ).stronglyMeasurable).norm.measurable
  have hmajor : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant (Ad L) F q r) μ ∧
      ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
    intro L q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
    have hmeas := fp81s21_rs_bv_variation_majorant_aemeasurable μ (Ad L) F q r hqr
      (hsection L) hFm (by
        filter_upwards [hgood, hFc] with ω hg hf
        exact ⟨(hg L q r hq hqr hr).1.norm, hf.mono (Icc_subset_Icc hq hr)⟩)
    have hbound : ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
      filter_upwards [hV] with ω hω
      exact fp81s21_projected_heat_variation_majorant_le γ hγ (Pj L) (hP L) Ψ hΨ Y F ω
        (V ω) hω.1 hω.2 hq hqr hr
    refine ⟨hMint.mono' hmeas.aestronglyMeasurable ?_, hbound⟩
    filter_upwards [hbound] with ω hb
    have hsup : 0 ≤ ⨆ t : Icc q r, ‖Ad L ω t‖ := by
      have hbd : BddAbove (Set.range (fun t : Icc q r => ‖Ad L ω t‖)) := by
        refine ⟨cbNorm 5 Ψ, ?_⟩
        rintro _ ⟨t, rfl⟩
        exact fp81s21_projected_heat_gradient_norm_le γ hγ (Pj L) (hP L) Ψ hΨ t (Y ω t)
      exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, hqr⟩)
    have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant (Ad L) F q r ω :=
      mul_nonneg hsup ENNReal.toReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hb
  refine ⟨M, hMint, ?_⟩
  intro L
  refine ⟨⟨fp81s21_rsbv_window_of_bv μ H (Ad L) F ?_ ?_ ?_⟩, hmajor L⟩
  · intro q r hq hqr hr
    exact fp81s21_projected_heat_increment_measurable γ hγ Ψ hΨ (Pj L) Y F hYm hFm
  · intro q r hq hqr hr
    filter_upwards [hgood] with ω hg
    exact hg L q r hq hqr.le hr
  · intro q r hq hqr hr
    exact (hmajor L q r hq hqr.le hr).1

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_rsbv_window
