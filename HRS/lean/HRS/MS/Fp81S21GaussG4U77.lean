import HRS.MS.Fp81S21GaussG4U76

/-! The centered initial estimate for finite Hermite combinations. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S53

/-- The centered initial G4 estimate for every finite oscillator combination. -/
theorem fp81s21_g4_initial_combo (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
          ∀ v w, 0 ≤ v → v ≤ w →
            fp81s21_g4_initialValue R f v w ≤
              A * (w-v)^2 * fp81s21_g4_J p.d f) := by
  obtain ⟨δi, hδi, hδihalf, hintegrand⟩ :=
    fp81s21_g4_initial_integrand_bound p
  obtain ⟨δd, hδd, hδdhalf, hduhamel⟩ :=
    fp81s21_g4_duhamel_combo p
  obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  let δ0 : ℝ := min δi (min δd δc)
  have hδ0 : 0 < δ0 := lt_min hδi (lt_min hδd hδc)
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left δi (min δd δc)).trans hδihalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδile : δ ≤ δi := hδle.trans (min_le_left δi (min δd δc))
  have hδdle : δ ≤ δd := hδle.trans
    ((min_le_right δi (min δd δc)).trans (min_le_left δd δc))
  have hδcle : δ ≤ δc := hδle.trans
    ((min_le_right δi (min δd δc)).trans (min_le_right δd δc))
  obtain ⟨A, hA, hperTime⟩ := hintegrand δ hδ hδile R
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδcle R.ρβ R.thermal
  refine ⟨A, hA, ?_⟩
  intro f hf v w hv hvw
  have hw : 0 ≤ w := hv.trans hvw
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμstar : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstar
  let ν : Measure ℝ := volume.restrict (Icc v w)
  letI : IsFiniteMeasure ν := Real.isFiniteMeasure_restrict_Icc v w
  let g : ℝ → Euc p.d → ℝ := fun q x =>
    r26t3_U R 0 (s53_clamp w q)
      (generatorW (r26t3_coeff R) (s53_clamp w q) f) x
  let D : Euc p.d → ℝ := fun x => r26t3_U R 0 w f x - r26t3_U R 0 v f x
  obtain ⟨Braw, hBraw, hrawBound, hrawProd⟩ :=
    fp81s21_g4_initial_scalar_prod_integrable p R hterm hf hw
  have hgbound : ∀ q x, |g q x| ≤ Braw := by
    intro q x
    exact hrawBound (s53_clamp w q) (s53_clamp_mem hw q) x
  have hjoint := fp81s21_g4_initial_scalar_joint_meas p R hterm hf hw
  let clampSubtype : ℝ → Icc (0 : ℝ) w := fun t =>
    ⟨s53_clamp w t, s53_clamp_mem hw t⟩
  have hclamp : Measurable clampSubtype :=
    ((s53_clamp_lip w).continuous.subtype_mk fun t => s53_clamp_mem hw t).measurable
  have hmap : Measurable (fun z : ℝ × Euc p.d => (clampSubtype z.1, z.2)) :=
    (hclamp.comp measurable_fst).prodMk measurable_snd
  have hgmeas : Measurable (Function.uncurry g) := by
    have heq : Function.uncurry g =
        Function.uncurry (fun q : Icc (0 : ℝ) w => fun x =>
          r26t3_U R 0 q.1 (generatorW (r26t3_coeff R) q.1 f) x) ∘
          (fun z : ℝ × Euc p.d => (clampSubtype z.1, z.2)) := by
      funext z
      simp [Function.uncurry, g, clampSubtype]
    rw [heq]
    exact hjoint.comp hmap
  have htimeSubset : Icc v w ⊆ Icc (0 : ℝ) w := by
    intro q hq
    exact ⟨le_trans hv hq.1, hq.2⟩
  have hνle : ν ≤ volume.restrict (Icc (0 : ℝ) w) := by
    exact Measure.restrict_mono_set volume htimeSubset
  have hprodle : ν.prod μstar ≤ (volume.restrict (Icc (0 : ℝ) w)).prod μstar :=
    Measure.prod_mono hνle le_rfl
  have hgprod0 : Integrable (Function.uncurry g)
      ((volume.restrict (Icc (0 : ℝ) w)).prod μstar) := by
    change Integrable
      (fun z : ℝ × Euc p.d =>
        r26t3_U R 0 (s53_clamp w z.1)
          (generatorW (r26t3_coeff R) (s53_clamp w z.1) f) z.2)
      ((volume.restrict (Icc (0 : ℝ) w)).prod μstar)
    simpa [μstar] using hrawProd
  have hgprod : Integrable (Function.uncurry g) (ν.prod μstar) :=
    hgprod0.mono_measure hprodle
  have hduhamelPoint :=
    hduhamel δ hδ hδdle R f hf 0 v w le_rfl hv hvw
  have hDuhamel : ∀ x, D x = ∫ q, g q x ∂ν := by
    intro x
    calc
      D x = ∫ q in Icc v w,
          r26t3_U R 0 q (generatorW (r26t3_coeff R) q f) x ∂volume := by
        simpa [D] using (hduhamelPoint x).2
      _ = ∫ q, r26t3_U R 0 q
          (generatorW (r26t3_coeff R) q f) x ∂ν := rfl
      _ = ∫ q, g q x ∂ν := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with q hq
        have hq0w : q ∈ Icc (0 : ℝ) w := ⟨le_trans hv hq.1, hq.2⟩
        simp [g, s53_clamp_of_mem hq0w]
  have hzero : ν ({0} : Set ℝ) = 0 := by
    dsimp [ν]
    rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left (by simp)
  have hqmem : ∀ᵐ q ∂ν, q ∈ Icc v w :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have hqne : ∀ᵐ q ∂ν, q ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hcenter : ∀ᵐ q ∂ν,
      (∫ x, (HRS.Whole.projMean μstar (g q) x)^2 ∂μstar) ≤
        A * fp81s21_g4_J p.d f := by
    filter_upwards [hqmem, hqne] with q hq hqne0
    have hq0 : 0 ≤ q := le_trans hv hq.1
    have hqpos : 0 < q := by
      by_contra hn
      have hqeq : q = 0 := by linarith
      exact hqne0 hqeq
    have hb := hperTime q hqpos f hf
    have hq0w : q ∈ Icc (0 : ℝ) w := ⟨hq0, hq.2⟩
    simpa [g, s53_clamp_of_mem hq0w] using hb
  have hK : 0 ≤ A * fp81s21_g4_J p.d f :=
    mul_nonneg hA (fp81s21_g4J_nonneg p.d f)
  have hcentered := fp81s21_g4_centered_time_integral_bound
    ν μstar g D Braw (A * fp81s21_g4_J p.d f) hBraw hK
    hgmeas hgprod hgbound hDuhamel hcenter
  have hlen : ν.real Set.univ = w - v := by
    simp [ν, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hvw)]
  have hmain : fp81s21_g4_initialValue R f v w ≤
      (A * fp81s21_g4_J p.d f) * (w-v)^2 := by
    simpa [fp81s21_g4_initialValue, μstar, D, hlen] using hcentered
  calc
    fp81s21_g4_initialValue R f v w ≤
        (A * fp81s21_g4_J p.d f) * (w-v)^2 := hmain
    _ = A * (w-v)^2 * fp81s21_g4_J p.d f := by ring

#print axioms fp81s21_g4_initial_combo
end HRS.Fp81.S21
