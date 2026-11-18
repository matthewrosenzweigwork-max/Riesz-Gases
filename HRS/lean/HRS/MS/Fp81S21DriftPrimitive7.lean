import HRS.MS.Fp81S21DriftPrimitive6

/-! Simultaneous source integrability, primitive identity and continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- Product-integrable measurable extensions and the simultaneous FTC imply
one event carrying every window-time identity and continuity. -/
theorem fp81s21_source_drift_primitive_ae
    {Ω : Type*} [MeasurableSpace Ω] {b T : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T)
    (Q : ℝ × Ω → ℝ) (K : (ℝ × ℝ) × Ω → ℝ)
    (Z : ℝ → ℝ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hQ : Measurable Q) (hK : Measurable K)
    (hQprod : Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod P))
    (hKprod : Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
      (volume.restrict (Icc (0 : ℝ) T))).prod P))
    (hFTC : ∀ᵐ ω ∂P, ∀ v ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc v T,
      Z v t ω = Q (v, ω) + ∫ s in v..t, K ((v, s), ω)) :
    ∀ᵐ ω ∂P, (∀ t ∈ Icc b T,
      IntervalIntegrable (fun v => Z v t ω) volume b t ∧
      (∫ v in b..t, Z v t ω) =
        ∫ s in b..t, Q (s, ω) + ∫ v in b..s, K ((v, s), ω)) ∧
      ContinuousOn (fun t => ∫ v in b..t, Z v t ω) (Icc b T) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let μ : Measure ℝ := volume.restrict (Icc b T)
  haveI : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hμν : μ ≤ ν := Measure.restrict_mono (Icc_subset_Icc hb le_rfl) le_rfl
  have hQsection : ∀ᵐ ω ∂P, Integrable (fun v => Q (v, ω)) ν := by
    have h := hQprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  have hKsection : ∀ᵐ ω ∂P,
      Integrable (fun z : ℝ × ℝ => K (z, ω)) (ν.prod ν) := by
    have h := hKprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  have hZ := fp81s21_source_identity_interval_integrable_measurable_extensions
    Q K Z P hQprod hKprod hQ hK hFTC
  filter_upwards [hQsection, hKsection, hFTC, hZ] with ω hQω hKω hFTCω hZω
  have hQb : IntegrableOn (fun v => Q (v, ω)) (Icc b T) := hQω.mono_measure hμν
  have hKb : Integrable (fun z : ℝ × ℝ => K (z, ω)) (μ.prod μ) :=
    hKω.mono_measure (Measure.prod_mono hμν hμν)
  have hZb : ∀ t ∈ Icc b T, IntervalIntegrable (fun v => Z v t ω) volume b t := by
    intro t ht
    exact hZω b t hb ht.1 ht.2
  have hFTCb : ∀ v t, b ≤ v → v ≤ t → t ≤ T →
      Z v t ω = Q (v, ω) + ∫ s in v..t, K ((v, s), ω) := by
    intro v t hv hvt ht
    exact hFTCω v ⟨hb.trans hv, hvt.trans ht⟩ t ⟨hvt, ht⟩
  obtain ⟨hIdentity, hCont⟩ := fp81s21_drift_primitive_of_source_identity hbT
    (fun v => Q (v, ω)) (fun z => K (z, ω)) (fun v t => Z v t ω)
    hQb hKb hZb hFTCb
  exact ⟨fun t ht => ⟨hZb t ht, hIdentity t ht⟩, hCont⟩

#print axioms fp81s21_source_drift_primitive_ae
end HRS.Fp81.S21
end
