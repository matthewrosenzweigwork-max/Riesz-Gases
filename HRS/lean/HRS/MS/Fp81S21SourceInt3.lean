import HRS.MS.Fp81S21SourceInt2

/-! Interval integrability from a frozen-source domination certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The physical propagated quadratic field for one oscillator coordinate. -/
def fp81s21_window_mode_source_field
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (α : MultiIndex p.d) : ℝ → ℝ → A.Ω → ℝ :=
  fun v t ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
    (propagatorW (r26t3_coeff R) v t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))

/-- For a fixed sample, a source-field bound by an integrable initial slice
plus the row-integral of an integrable kernel gives interval integrability on
every subinterval, simultaneously for all terminal times. -/
theorem fp81s21_source_dominance_interval_integrable
    {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}
    (Q : ℝ × Ω → ℝ) (K : (ℝ × ℝ) × Ω → ℝ)
    (Z : ℝ → ℝ → Ω → ℝ) (ω : Ω)
    (hQω : Integrable (fun v => Q (v, ω)) (volume.restrict (Icc (0 : ℝ) T)))
    (hKω : Integrable (fun z : ℝ × ℝ => K (z, ω))
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    (hZmeas : Measurable (fun z : (ℝ × ℝ) × Ω => Z z.1.1 z.1.2 z.2))
    (hDom : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) T)),
      ‖Z v t ω‖ ≤ ‖Q (v, ω)‖ +
        ∫ s, ‖K ((v, s), ω)‖ ∂(volume.restrict (Icc (0 : ℝ) T))) :
    ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ T →
      IntervalIntegrable (fun v => Z v t ω) volume a t := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hRow : Integrable
      (fun v => ∫ s, ‖K ((v, s), ω)‖ ∂ν) ν := hKω.integral_norm_prod_left
  have hMajor : Integrable
      (fun v => ‖Q (v, ω)‖ + ∫ s, ‖K ((v, s), ω)‖ ∂ν) ν := hQω.norm.add hRow
  intro a t ha hat ht
  have htmem : t ∈ Icc (0 : ℝ) T := ⟨ha.trans hat, ht⟩
  have hMap : Measurable (fun v : ℝ => ((v, t), ω)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  have hZsection : AEMeasurable (fun v => Z v t ω) ν :=
    (hZmeas.comp hMap).aemeasurable
  have hZint : Integrable (fun v => Z v t ω) ν := by
    refine Integrable.mono' hMajor hZsection.aestronglyMeasurable ?_
    filter_upwards [hDom t htmem] with v hv
    simpa [ν] using hv
  have hOn : IntegrableOn (fun v => Z v t ω) (Icc (0 : ℝ) T) volume := hZint
  have hOnSub : IntegrableOn (fun v => Z v t ω) (Icc a t) volume :=
    hOn.mono_set (Icc_subset_Icc ha ht)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hat).2 hOnSub

/-- For the actual frozen-source quadratic field, product integrability and a
uniform-in-terminal-time source domination certificate give all interval
integrability statements on one particle-probability event. The domination
certificate is the remaining input to be supplied by the Sup43 frozen-source
identity together with the zero-extension agreements. -/
theorem fp81s21_window_mode_source_interval_integrable_of_domination
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hT : 0 < T) {N : ℕ} (A : Particle R N) (α : MultiIndex p.d)
    (Q : ℝ × A.Ω → ℝ) (K : (ℝ × ℝ) × A.Ω → ℝ)
    (hQprod : Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod A.P))
    (hKprod : Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
      (volume.restrict (Icc (0 : ℝ) T))).prod A.P))
    (hZmeas : Measurable (fun z : (ℝ × ℝ) × A.Ω =>
      fp81s21_window_mode_source_field p R A α z.1.1 z.1.2 z.2))
    (hDom : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) T)),
        ‖fp81s21_window_mode_source_field p R A α v t ω‖ ≤ ‖Q (v, ω)‖ +
          ∫ s, ‖K ((v, s), ω)‖ ∂(volume.restrict (Icc (0 : ℝ) T))) :
    ∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ T →
      IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  have hQsection : ∀ᵐ ω ∂A.P, Integrable (fun v => Q (v, ω)) ν := by
    have h := hQprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  have hKsection : ∀ᵐ ω ∂A.P,
      Integrable (fun z : ℝ × ℝ => K (z, ω)) (ν.prod ν) := by
    have h := hKprod.swap.prod_right_ae
    simpa [Function.comp_def, ν] using h
  filter_upwards [hQsection, hKsection, hDom] with ω hQω hKω hDomω
  exact fp81s21_source_dominance_interval_integrable Q K
    (fp81s21_window_mode_source_field p R A α) ω hQω hKω hZmeas hDomω

#print axioms fp81s21_source_dominance_interval_integrable
#print axioms fp81s21_window_mode_source_interval_integrable_of_domination
end HRS.Fp81.S21
end
