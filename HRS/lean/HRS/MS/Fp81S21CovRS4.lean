import HRS.MS.Fp81S21CovRS3
import HRS.MS.Fp81S21DriftRS9

/-! Measurable BV covariance RS windows with a uniform integrable majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Projected heat Hessians paired with a measurable projective cumulative have
selected scalar RS families. Their exact supremum-times-variation majorants
are integrable on every admissible interval and bounded by one integrable
function independent of the projection. -/
theorem fp81s21_projected_heat_covariance_rsbv_window
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {m H : ℝ}
    (μ : Measure Ω) (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hP : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y : Ω → ℝ → OscPath d m H)
    (F : Ω → ℝ → projTensor (OscPath d m H) 2)
    (V : Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Y ω t))
    (hFm : ∀ t, Measurable (fun ω => F ω t))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (Y ω) (Icc 0 H))
    (hFc : ∀ᵐ ω ∂μ, ContinuousOn (F ω) (Icc 0 H))
    (hVint : Integrable V μ)
    (hV : ∀ᵐ ω ∂μ, BoundedVariationOn (F ω) (Icc 0 H) ∧
      (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V ω) :
    let Ad := fun L ω τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ))
    ∃ M : Ω → ℝ, Integrable M μ ∧ ∀ L,
      Nonempty (fp81s21_RSBVWindow μ H (Ad L) F) ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        Integrable (fp81s21_rs_bv_variation_majorant (Ad L) F q r) μ ∧
        ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
  classical
  let B := OscPath d m H
  haveI : SecondCountableTopology B := by infer_instance
  haveI : SecondCountableTopology (projTensor B 2) :=
    HRS.MS.R26T3.s21g2_k06_sc (B := B) 2
  letI : MeasurableAdd₂ (projTensor B 2) := ⟨continuous_add.measurable⟩
  let Ad : ℕ → Ω → ℝ → projTensor B 2 →L[ℝ] ℝ := fun L ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ))
  let M : Ω → ℝ := fun ω => cbNorm 5 Ψ * V ω
  have hMint : Integrable M μ := hVint.const_mul _
  have hgood : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      ∀ᵐ ω ∂μ, ContinuousOn (Ad L ω) (Icc q r) ∧
        BoundedVariationOn (F ω) (Icc q r) := by
    intro L q r hq hqr hr
    filter_upwards [hYc, hFc, hV] with ω hy hf hv
    have hs : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
    exact ⟨(fp81s21_projected_heat_covariance_pairing_continuousOn γ hγ
      Pj hP hconv hLP Ψ hΨ L (Y ω) hy).mono hs, hv.1.mono hs⟩
  have hsection : ∀ L τ, Measurable (fun ω => ‖Ad L ω τ‖) := by
    intro L τ
    have hΨP : MemCb 5 (fun w => Ψ (Pj L w)) :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Pj L) hΨ).1
    letI := hγ τ
    have hdiff : ContDiff ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) :=
      ((s102_r2HeatFn_derivs γ τ hΨP).1).of_le (by norm_num)
    have hD : Continuous (iteratedFDeriv ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ)) :=
      hdiff.continuous_iteratedFDeriv (by norm_num)
    have hA : Continuous (fun y : B => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) y)) :=
      fp81s21_covariance_pairingCLM_continuous.comp hD
    exact (hA.comp_stronglyMeasurable (hYm τ).stronglyMeasurable).norm.measurable
  have hmajor : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant (Ad L) F q r) μ ∧
      ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
    intro L q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
    have hmeas := fp81s21_rs_bv_variation_majorant_aemeasurable μ (Ad L) F q r hqr
      (hsection L) hFm (by
        filter_upwards [hgood L q r hq hqr hr, hFc] with ω hg hf
        exact ⟨hg.1.norm, hf.mono (Icc_subset_Icc hq hr)⟩)
    have hbound : ∀ᵐ ω ∂μ,
        fp81s21_rs_bv_variation_majorant (Ad L) F q r ω ≤ M ω := by
      filter_upwards [hV] with ω hω
      exact fp81s21_projected_heat_covariance_variation_majorant_le γ hγ
        (Pj L) (hP L) Ψ hΨ Y F ω (V ω) hω.1 hω.2 hq hqr hr
    refine ⟨hMint.mono' hmeas.aestronglyMeasurable ?_, hbound⟩
    filter_upwards [hbound] with ω hb
    have hsup : 0 ≤ ⨆ τ : Icc q r, ‖Ad L ω τ‖ := by
      have hbd : BddAbove (Set.range (fun τ : Icc q r => ‖Ad L ω τ‖)) := by
        refine ⟨cbNorm 5 Ψ, ?_⟩
        rintro _ ⟨τ, rfl⟩
        exact fp81s21_projected_heat_covariance_pairing_norm_le γ hγ
          (Pj L) (hP L) Ψ hΨ τ (Y ω τ)
      exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, hqr⟩)
    have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant (Ad L) F q r ω := by
      unfold fp81s21_rs_bv_variation_majorant
      exact mul_nonneg hsup ENNReal.toReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hb
  have hΨP : ∀ L, MemCb 5 (fun w => Ψ (Pj L w)) := by
    intro L
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Pj L) hΨ).1
  have hS : ∀ L q r, 0 ≤ q → q < r → r ≤ H →
      ∀ τ u v, Measurable (fun ω => Ad L ω τ (F ω v - F ω u)) := by
    intro L q r hq hqr hr τ u v
    have hheat : ∀ τ, ContDiff ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) := by
      intro τ
      letI := hγ τ
      exact ((s102_r2HeatFn_derivs γ τ (hΨP L)).1).of_le (by norm_num)
    exact fp81s21_covariance_derivative_increment_measurable
      (fun τ => r2HeatFn γ (fun w => Ψ (Pj L w)) τ) Y F hheat
      (fun τ => (hYm τ).stronglyMeasurable) (fun t => (hFm t).stronglyMeasurable)
      τ u v
  have hgoodRS : ∀ L q r, 0 ≤ q → q < r → r ≤ H →
      ∀ᵐ ω ∂μ, ContinuousOn (Ad L ω) (Icc q r) ∧
        BoundedVariationOn (F ω) (Icc q r) := by
    intro L q r hq hqr hr
    filter_upwards [hgood L q r hq hqr.le hr] with ω hg
    exact hg
  have hmaj : ∀ L q r, 0 ≤ q → q < r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant (Ad L) F q r) μ := by
    intro L q r hq hqr hr
    exact (hmajor L q r hq hqr.le hr).1
  refine ⟨M, hMint, ?_⟩
  intro L
  refine ⟨⟨fp81s21_rsbv_window_of_bv μ H (Ad L) F (hS L) (hgoodRS L) (hmaj L)⟩, ?_⟩
  intro q r hq hqr hr
  exact hmajor L q r hq hqr hr

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_covariance_rsbv_window
end
