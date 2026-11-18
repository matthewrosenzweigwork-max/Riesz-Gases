import HRS.MD.EQBurnBurnTrace
import HRS.ME.RetWeight

/-!
# Row 5.10, shifted burn-in, part A: the `L²` form of the time-integrated trace discrepancy

`rbs_trace_L2`: for a stationary Gibbs flow filtered by `ℱ` and a fixed `β`, the second moment of the time integral
`∫_0^{a+T} e^{-2c(a-r)_+} ‖Σ_N^r - C̄^r‖₁ dr` is at most `(C b_N)²`, uniformly in `ρβ, a, N` (stationarity, the measurable
majorant `traceMaj`, Cauchy-Schwarz in time against the finite measure `e^{-2c(a-r)_+} dr`, Tonelli and `eqtrace_key`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQTrace HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

theorem rbs_sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy-Schwarz against a weight: `(∫ G f)² ≤ (∫ G) ∫ G f²`. -/
theorem rbs_cs_weighted {α : Type*} [MeasurableSpace α] (μ : Measure α) {G f : α → ℝ≥0∞}
    (hG : Measurable G) (hf : Measurable f) :
    (∫⁻ r, G r * f r ∂μ) ^ 2 ≤ (∫⁻ r, G r ∂μ) * ∫⁻ r, G r * f r ^ 2 ∂μ := by
  have h := lintegral_mul_le_L2 (μ.withDensity G) (w := fun _ => (1 : ℝ≥0∞)) (F := f)
    aemeasurable_const hf.aemeasurable
  simp only [one_mul, one_pow] at h
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hf] at h
  rw [lintegral_withDensity_eq_lintegral_mul _ hG (hf.pow_const 2)] at h
  have h1 : (∫⁻ r, (1 : ℝ≥0∞) ∂(μ.withDensity G)) = ∫⁻ r, G r ∂μ := by
    rw [lintegral_const, one_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [h1] at h
  simp only [Pi.mul_apply] at h
  calc (∫⁻ r, G r * f r ∂μ) ^ 2 ≤ ((∫⁻ r, G r ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ r, G r * f r ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, rbs_sq_rpow_half, rbs_sq_rpow_half]

theorem rbs_trace_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (m : ℝ) (hm : (d : ℝ) + 1 < m) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
          ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal ρβ)))) ^ 2 ∂P ≤
          ENNReal.ofReal (((1 / (2 * c) + T) * C * bracketBias d s N) ^ 2) := by
  obtain ⟨C₀, hC₀, hk⟩ := eqtrace_key hd hs0 hsd V hV β β hβ le_rfl m hm
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  refine ⟨C₀, hC₀, ?_⟩
  intro ρβ hρ a ha N hN Ω _ P _ X₀ W X hX ℱ W' hF
  obtain ⟨hρc, hρp, hPr⟩ := eqtrace_setup hd hs0 hsd V hV β β hβ le_rfl β hβI ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hN1 : 1 ≤ N := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < m := by linarith
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  set S : ℝ := a + T with hS
  have hS0 : 0 ≤ S := by positivity
  have hstat := MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ S hN P X₀ W X hX
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le r) le_rfl
  set f : Config d N → ℝ≥0∞ := fun X => traceMaj m β⁻¹ ρβ X with hf
  have hfm : Measurable f := measurable_traceMaj hM2 hq hρc hN1
  set G : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable (fun r : ℝ => max (a - r) 0) :=
      (measurable_const.sub measurable_id).max measurable_const
    exact (Real.measurable_exp.comp (measurable_const.mul h1)).pow_const 2
  have hmaj : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S,
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ)))) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) S, G r * f (X (min S r).toNNReal ω) := by
    intro ω
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [min_eq_right hr.2, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact traceNorm_le_maj hd hm hq hρc hρp hN1 _
  obtain ⟨ℱ', W'', hfs⟩ : ∃ (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
      (W'' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ' W'' W X := ⟨ℱ, W', hF⟩
  have hYm : Measurable (fun p : ℝ × Ω => X (min S p.1).toNNReal p.2) :=
    HRS.MD.EQRem.eqrem_joint_meas ℱ' S X hfs.progressive
  have hFm : Measurable (fun p : ℝ × Ω => f (X (min S p.1).toNNReal p.2)) := hfm.comp hYm
  have hgm : Measurable (fun p : ℝ × Ω => G p.1 * f (X (min S p.1).toNNReal p.2) ^ 2) :=
    (hGm.comp measurable_fst).mul (hFm.pow_const 2)
  set μ : ℝ≥0∞ := ∫⁻ r in Set.Icc (0 : ℝ) S, G r with hμ
  have hμle : μ ≤ ENNReal.ofReal (1 / (2 * c) + T) := eqb_exp_lintegral_le hc ha hT
  have hμtop : μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμle
  have hCb : 0 ≤ C₀ * bracketBias d s N := mul_nonneg hC₀.le hb0
  -- Cauchy-Schwarz pointwise in `ω`
  have hCS : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, G r * f (X (min S r).toNNReal ω)) ^ 2 ≤
      μ * ∫⁻ r in Set.Icc (0 : ℝ) S, G r * f (X (min S r).toNNReal ω) ^ 2 := fun ω =>
    rbs_cs_weighted (volume.restrict (Set.Icc (0 : ℝ) S)) hGm
      (hfm.comp (hYm.comp (measurable_id.prodMk measurable_const)))
  have hint : ∀ r ∈ Set.Icc (0 : ℝ) S, ∫⁻ ω, f (X (min S r).toNNReal ω) ^ 2 ∂P ≤
      ENNReal.ofReal ((C₀ * bracketBias d s N) ^ 2) := by
    intro r hr
    have hr' : ((min S r).toNNReal : ℝ) ≤ S := by
      rw [Real.coe_toNNReal _ (le_min hS0 hr.1)]; exact min_le_left _ _
    have h1 := hstat _ hr'
    calc ∫⁻ ω, f (X (min S r).toNNReal ω) ^ 2 ∂P
        = ∫⁻ x, f x ^ 2 ∂(P.map (X (min S r).toNNReal)) :=
          (lintegral_map (hfm.pow_const 2) (hXm _)).symm
      _ ≤ _ := by rw [h1]; exact hk β hβI ρβ hρ N hN
  calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S,
          ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal ρβ)))) ^ 2 ∂P
      ≤ ∫⁻ ω, μ * (∫⁻ r in Set.Icc (0 : ℝ) S, G r * f (X (min S r).toNNReal ω) ^ 2) ∂P :=
        lintegral_mono fun ω => (pow_le_pow_left' (hmaj ω) 2).trans (hCS ω)
    _ = μ * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, G r * f (X (min S r).toNNReal ω) ^ 2) ∂P := by
        exact lintegral_const_mul' _ _ hμtop
    _ = μ * ∫⁻ r in Set.Icc (0 : ℝ) S, (∫⁻ ω, G r * f (X (min S r).toNNReal ω) ^ 2 ∂P) := by
        congr 1
        exact (lintegral_lintegral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) S)) (ν := P)
          (f := fun r ω => G r * f (X (min S r).toNNReal ω) ^ 2) hgm.aemeasurable).symm
    _ ≤ μ * ∫⁻ r in Set.Icc (0 : ℝ) S, G r * ENNReal.ofReal ((C₀ * bracketBias d s N) ^ 2) := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) μ
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact hint r hr
    _ = μ * (μ * ENNReal.ofReal ((C₀ * bracketBias d s N) ^ 2)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / (2 * c) + T) * (ENNReal.ofReal (1 / (2 * c) + T) *
          ENNReal.ofReal ((C₀ * bracketBias d s N) ^ 2)) := by gcongr
    _ = ENNReal.ofReal (((1 / (2 * c) + T) * C₀ * bracketBias d s N) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end HRS.ME.Ret

end
