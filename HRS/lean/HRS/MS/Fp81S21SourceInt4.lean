import HRS.MS.Fp81S21SourceInt3

/-! Interval integrability from the exact frozen-source identity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- On a Fubini section, the frozen-source identity and the product `L¹`
kernel bound imply integrability of the physical source field on every
`[a,t]` in one event. -/
theorem fp81s21_source_identity_interval_integrable
    {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}
    (Q : ℝ × Ω → ℝ) (K : (ℝ × ℝ) × Ω → ℝ)
    (Z : ℝ → ℝ → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hQprod : Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod P))
    (hKprod : Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
      (volume.restrict (Icc (0 : ℝ) T))).prod P))
    (hZmeas : Measurable (fun z : (ℝ × ℝ) × Ω => Z z.1.1 z.1.2 z.2))
    (hFTC : ∀ᵐ ω ∂P, ∀ v ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc v T,
      Z v t ω = Q (v, ω) + ∫ s in v..t, K ((v, s), ω)) :
    ∀ᵐ ω ∂P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ T →
      IntervalIntegrable (fun v => Z v t ω) volume a t := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hQsection : ∀ᵐ ω ∂P, Integrable (fun v => Q (v, ω)) ν := by
    have h := hQprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  have hKsection : ∀ᵐ ω ∂P,
      Integrable (fun z : ℝ × ℝ => K (z, ω)) (ν.prod ν) := by
    have h := hKprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  filter_upwards [hQsection, hKsection, hFTC] with ω hQω hKω hFTCω
  let row : ℝ → ℝ := fun v => ∫ s, ‖K ((v, s), ω)‖ ∂ν
  have hrow : Integrable row ν := hKω.integral_norm_prod_left
  have hmajor : Integrable (fun v => ‖Q (v, ω)‖ + row v) ν := hQω.norm.add hrow
  intro a t ha hat ht
  have htmem : t ∈ Icc (0 : ℝ) T := ⟨ha.trans hat, ht⟩
  let Zt : ℝ → ℝ := fun v => Z v t ω
  have hMap : Measurable (fun v : ℝ => ((v, t), ω)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  let νt : Measure ℝ := ν.restrict (Icc (0 : ℝ) t)
  have hmajorT : Integrable (fun v => ‖Q (v, ω)‖ + row v) νt := hmajor.restrict
  have hDomT : ∀ᵐ v ∂νt, ‖Z v t ω‖ ≤ ‖Q (v, ω)‖ + row v := by
    have hRows : ∀ᵐ v ∂ν, Integrable (fun s => K ((v, s), ω)) ν :=
      hKω.prod_right_ae
    have hRowsT : ∀ᵐ v ∂νt, Integrable (fun s => K ((v, s), ω)) ν :=
      ae_mono Measure.restrict_le_self hRows
    filter_upwards [hRowsT, ae_restrict_mem measurableSet_Icc] with v hvRow hv
    rcases hv with ⟨hv0, hvt⟩
    have hvt' : v ≤ t := hvt
    have hFTCvt := hFTCω v ⟨hv0, le_trans hvt' ht⟩ t ⟨hvt', ht⟩
    have hNormInt : Integrable (fun s => ‖K ((v, s), ω)‖) ν := hvRow.norm
    have hNormOn : IntegrableOn (fun s => ‖K ((v, s), ω)‖)
        (Icc (0 : ℝ) T) volume := hNormInt
    have hIocSubset : Ioc v t ⊆ Icc (0 : ℝ) T := by
      intro s hs
      exact ⟨le_trans hv0 hs.1.le, hs.2.trans ht⟩
    have hSetLe : (∫ s in Ioc v t, ‖K ((v, s), ω)‖ ∂volume) ≤
        ∫ s in Icc (0 : ℝ) T, ‖K ((v, s), ω)‖ ∂volume :=
      setIntegral_mono_set hNormOn
        (Filter.Eventually.of_forall fun s => norm_nonneg (K ((v, s), ω)))
        hIocSubset.eventuallySubset
    have hIntervalLe : (∫ s in v..t, ‖K ((v, s), ω)‖) ≤ row v := by
      rw [intervalIntegral.integral_of_le hvt']
      simpa [row, ν] using hSetLe
    calc
      ‖Z v t ω‖ = ‖Q (v, ω) + ∫ s in v..t, K ((v, s), ω)‖ := by rw [hFTCvt]
      _ ≤ ‖Q (v, ω)‖ + ‖∫ s in v..t, K ((v, s), ω)‖ := norm_add_le _ _
      _ ≤ ‖Q (v, ω)‖ + ∫ s in v..t, ‖K ((v, s), ω)‖ :=
        add_le_add (le_refl _) (intervalIntegral.norm_integral_le_integral_norm hvt')
      _ ≤ ‖Q (v, ω)‖ + row v := by linarith [hIntervalLe]
  have hZtT : Integrable Zt νt := by
    refine Integrable.mono' hmajorT (hZmeas.comp hMap).aestronglyMeasurable ?_
    filter_upwards [hDomT] with v hv
    simpa [Zt, row] using hv
  have hTset : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht
  have hOnT : IntegrableOn (fun v => Z v t ω) (Icc (0 : ℝ) t) volume := by
    change Integrable (fun v => Z v t ω) (volume.restrict (Icc (0 : ℝ) t))
    simpa [νt, ν, Measure.restrict_restrict_of_subset hTset] using hZtT
  have hOnSub : IntegrableOn (fun v => Z v t ω) (Icc a t) volume :=
    hOnT.mono_set (Icc_subset_Icc ha le_rfl)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hat).2 hOnSub

/-- The source identity theorem specialized to the propagated quadratic field. -/
theorem fp81s21_window_mode_source_interval_integrable_of_ftc
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ) (hT : 0 < T)
    {N : ℕ} (A : Particle R N) (α : MultiIndex p.d)
    (Q : ℝ × A.Ω → ℝ) (K : (ℝ × ℝ) × A.Ω → ℝ)
    (hQprod : Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod A.P))
    (hKprod : Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
      (volume.restrict (Icc (0 : ℝ) T))).prod A.P))
    (hZmeas : Measurable (fun z : (ℝ × ℝ) × A.Ω =>
      fp81s21_window_mode_source_field p R A α z.1.1 z.1.2 z.2))
    (hFTC : ∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc v T,
      fp81s21_window_mode_source_field p R A α v t ω = Q (v, ω) +
        ∫ s in v..t, K ((v, s), ω)) :
    ∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ T →
      IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t := by
  exact fp81s21_source_identity_interval_integrable Q K
    (fp81s21_window_mode_source_field p R A α) A.P hQprod hKprod hZmeas hFTC

#print axioms fp81s21_source_identity_interval_integrable
#print axioms fp81s21_window_mode_source_interval_integrable_of_ftc
end HRS.Fp81.S21
end
