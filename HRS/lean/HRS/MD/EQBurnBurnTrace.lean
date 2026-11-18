import HRS.MD.EQBurnBurnBase
import HRS.MD.EQTrace
import HRS.MD.EQRemInt13

/-!
# EQ-BURN P4, part 2: the time-integrated trace discrepancy

`eqb_trace_int`: for a stationary Gibbs flow filtered by `ℱ`, the quantity
`E ∫_0^{a+T} e^{-2c(a-r)_+} ‖Σ_N^r - C̄^r‖₁ dr` is at most `C b_N`, uniformly in `β, ρβ, a, N` (stationarity of the flow, the
measurable majorant `traceMaj`, Tonelli, `eqtrace_key`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQTrace HRS.MD.EQ29

variable {d : ℕ}

/-- The `L¹` bound for the measurable majorant. -/
theorem eqb_traceMaj_L1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) + 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, traceMaj M β⁻¹ ρβ X ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * bracketBias d s N) := by
  obtain ⟨C, hC, hk⟩ := eqtrace_key hd hs0 hsd V hV βm βp hβm hββ M hM
  have hsetup := eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ
  refine ⟨C, hC, fun β hβ ρβ hρ N hN => ?_⟩
  obtain ⟨hρc, hρp, hPr⟩ := hsetup β hβ ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 (lt_of_lt_of_le hβm hβ.1).le
  have hN1 : 1 ≤ N := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < M := by linarith
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  have hCb : 0 ≤ C * bracketBias d s N := mul_nonneg hC.le hb0
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  set f : Config d N → ℝ≥0∞ := fun X => traceMaj M β⁻¹ ρβ X with hf
  have hfm : Measurable f := measurable_traceMaj hM2 hq hρc hN1
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    hfm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h2 : ∫⁻ X, f X ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal ((C * bracketBias d s N) ^ 2) := by
    simpa [ENNReal.rpow_two, hf] using hk β hβ ρβ hρ N hN
  calc ∫⁻ X, f X ∂P ≤ (∫⁻ X, f X ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by simpa using hH
    _ ≤ (ENNReal.ofReal ((C * bracketBias d s N) ^ 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (C * bracketBias d s N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hCb]

theorem eqb_trace_int (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : (d : ℝ) + 1 < m) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
        ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
          ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal ρβ)))) ∂P ≤
          ENNReal.ofReal (C * bracketBias d s N) := by
  obtain ⟨C₀, hC₀, hk⟩ := eqb_traceMaj_L1 hd hs0 hsd V hV βm βp hβm hββ m hm
  refine ⟨C₀ * (1 / (2 * c) + T), by positivity, ?_⟩
  intro β hβ ρβ hρ a ha N hN Ω _ P _ X₀ W X hX ℱ W' hF
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  obtain ⟨hρc, hρp, hPr⟩ := eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ β hβ ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ0.le
  have hN1 : 1 ≤ N := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < m := by linarith
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  set S : ℝ := a + T with hS
  have hS0 : 0 ≤ S := by positivity
  have hstat := MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 S hN P X₀ W X hX
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le r) le_rfl
  set f : Config d N → ℝ≥0∞ := fun X => traceMaj m β⁻¹ ρβ X with hf
  have hfm : Measurable f := measurable_traceMaj hM2 hq hρc hN1
  -- pointwise majorant
  have hmaj : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S,
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ)))) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
        f (X (min S r).toNNReal ω) := by
    intro ω
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [min_eq_right hr.2, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact traceNorm_le_maj hd hm hq hρc hρp hN1 _
  -- joint measurability
  obtain ⟨ℱ', W'', hfs⟩ : ∃ (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
      (W'' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ' W'' W X := ⟨ℱ, W', hF⟩
  have hYm : Measurable (fun p : ℝ × Ω => X (min S p.1).toNNReal p.2) :=
    HRS.MD.EQRem.eqrem_joint_meas ℱ' S X hfs.progressive
  have hgm : Measurable (fun p : ℝ × Ω =>
      ENNReal.ofReal (Real.exp (-c * max (a - p.1) 0) ^ 2) * f (X (min S p.1).toNNReal p.2)) := by
    refine Measurable.mul ?_ (hfm.comp hYm)
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable (fun p : ℝ × Ω => max (a - p.1) 0) :=
      (measurable_const.sub measurable_fst).max measurable_const
    exact (Real.measurable_exp.comp (measurable_const.mul h1)).pow_const 2
  calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S,
          ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal ρβ)))) ∂P
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
          f (X (min S r).toNNReal ω)) ∂P := lintegral_mono hmaj
    _ = ∫⁻ r in Set.Icc (0 : ℝ) S, (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
          f (X (min S r).toNNReal ω) ∂P) :=
        (lintegral_lintegral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) S)) (ν := P)
          (f := fun r ω => ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
            f (X (min S r).toNNReal ω)) hgm.aemeasurable).symm
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
          ENNReal.ofReal (C₀ * bracketBias d s N) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        rw [lintegral_const_mul (f := fun ω => f (X (min S r).toNNReal ω)) _ (hfm.comp (hXm (min S r).toNNReal))]
        gcongr
        have hr' : ((min S r).toNNReal : ℝ) ≤ S := by
          rw [Real.coe_toNNReal _ (le_min hS0 hr.1)]; exact min_le_left _ _
        have := hstat _ hr'
        calc ∫⁻ ω, f (X (min S r).toNNReal ω) ∂P = ∫⁻ x, f x ∂(P.map (X (min S r).toNNReal)) :=
              (lintegral_map hfm (hXm _)).symm
          _ ≤ _ := by rw [this]; exact hk β hβ ρβ hρ N hN
    _ = (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2)) *
          ENNReal.ofReal (C₀ * bracketBias d s N) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / (2 * c) + T) * ENNReal.ofReal (C₀ * bracketBias d s N) :=
        by gcongr; exact eqb_exp_lintegral_le hc ha hT
    _ = ENNReal.ofReal (C₀ * (1 / (2 * c) + T) * bracketBias d s N) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end HRS.MD.EQBurnBurn

end
