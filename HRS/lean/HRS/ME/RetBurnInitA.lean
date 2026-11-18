import HRS.ME.RetEngine
import HRS.MD.EQBurnBurnMain

/-!
# Row 5.10, packet B3 (part A): auxiliary estimates for the retained initial field

* `ret_b3_trace_L2`: the second moment of the time integral of the measurable trace majorant over `[0,S]`, for a stationary
  Gibbs flow (stationarity, Cauchy-Schwarz in time, Tonelli);
* `ret_b3_remMeas`: almost-everywhere measurability of the remainder majorant.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn HRS.MD.EQTrace

variable {d : ℕ}

theorem ret_b3_rpow_half_sq (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy-Schwarz in time on an interval of length `S`. -/
theorem ret_b3_cs_time (S : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ r in Set.Icc (0 : ℝ) S, g r) ^ 2 ≤
      ENNReal.ofReal S * ∫⁻ r in Set.Icc (0 : ℝ) S, g r ^ 2 := by
  have h := lintegral_mul_le_L2 (volume.restrict (Set.Icc (0 : ℝ) S)) (w := fun _ => (1 : ℝ≥0∞)) (F := g)
    aemeasurable_const hg.aemeasurable
  simp only [one_mul, one_pow] at h
  have h2 := pow_le_pow_left' h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ret_b3_rpow_half_sq, ret_b3_rpow_half_sq]
  simp

/-- The abstract time-integral estimate: for a jointly measurable family `Y_r` and a measurable `f` with a uniform second moment
`B` at the times `r ∈ [0,S]`, the second moment of `∫_0^S f(Y_r) dr` is at most `S² B`. -/
theorem ret_b3_core {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℝ) (hS : 0 ≤ S) (Y : ℝ≥0 → Ω → E) (f : E → ℝ≥0∞) (hfm : Measurable f)
    (hYm : Measurable (fun p : ℝ × Ω => Y (min S p.1).toNNReal p.2)) (hXm : ∀ r : ℝ≥0, Measurable (Y r))
    (B : ℝ≥0∞) (hB : ∀ u : ℝ≥0, (u : ℝ) ≤ S → ∫⁻ ω, f (Y u ω) ^ 2 ∂P ≤ B) :
    Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, f (Y (min S r).toNNReal ω)) ∧
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, f (Y (min S r).toNNReal ω)) ^ 2 ∂P ≤
        ENNReal.ofReal S * (B * ENNReal.ofReal S) := by
  have hFm : Measurable (fun p : ℝ × Ω => f (Y (min S p.1).toNNReal p.2)) := hfm.comp hYm
  refine ⟨?_, ?_⟩
  · exact (hFm.comp (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) S))
  · have hFr : ∀ ω, Measurable (fun r : ℝ => f (Y (min S r).toNNReal ω)) := fun ω =>
      hFm.comp measurable_prodMk_right
    have hgm : Measurable (fun p : ℝ × Ω => f (Y (min S p.1).toNNReal p.2) ^ 2) := hFm.pow_const 2
    have hbound : ∀ r ∈ Set.Icc (0 : ℝ) S, ∫⁻ ω, f (Y (min S r).toNNReal ω) ^ 2 ∂P ≤ B := by
      intro r hr
      refine hB _ ?_
      rw [Real.coe_toNNReal _ (le_min hS hr.1)]; exact min_le_left _ _
    calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, f (Y (min S r).toNNReal ω)) ^ 2 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal S * ∫⁻ r in Set.Icc (0 : ℝ) S, f (Y (min S r).toNNReal ω) ^ 2) ∂P :=
          lintegral_mono fun ω => ret_b3_cs_time S _ (hFr ω)
      _ = ENNReal.ofReal S * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, f (Y (min S r).toNNReal ω) ^ 2) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal S * ∫⁻ r in Set.Icc (0 : ℝ) S, ∫⁻ ω, f (Y (min S r).toNNReal ω) ^ 2 ∂P := by
          congr 1
          exact (lintegral_lintegral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) S)) (ν := P)
            (f := fun r ω => f (Y (min S r).toNNReal ω) ^ 2) hgm.aemeasurable).symm
      _ ≤ ENNReal.ofReal S * ∫⁻ r in Set.Icc (0 : ℝ) S, B := by
          refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact hbound r hr
      _ = ENNReal.ofReal S * (B * ENNReal.ofReal S) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]

set_option maxHeartbeats 1600000 in
theorem ret_b3_trace_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) + 1 < m)
    {S : ℝ} (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρβ : Torus d → ℝ), IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ S X₀ W X →
        ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X →
        Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, traceMaj m β⁻¹ ρβ (X (min S r).toNNReal ω)) ∧
        (∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S,
            ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal ρβ)))) ≤
          ∫⁻ r in Set.Icc (0 : ℝ) S, traceMaj m β⁻¹ ρβ (X (min S r).toNNReal ω)) ∧
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, traceMaj m β⁻¹ ρβ (X (min S r).toNNReal ω)) ^ 2 ∂P ≤
          ENNReal.ofReal ((C * bracketBias d s N) ^ 2) := by
  obtain ⟨C₀, hC₀, hk⟩ := eqtrace_key hd hs0 hsd V hV β β hβ le_rfl m hm
  have hsetup := eqtrace_setup hd hs0 hsd V hV β β hβ le_rfl
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  refine ⟨(S + 1) * C₀, by positivity, ?_⟩
  intro ρβ hρ N hN Ω _ P _ X₀ W X hX ℱ W' hF
  obtain ⟨hρc, hρp, hPr⟩ := hsetup β hβI ρβ hρ N hN
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hN1 : 1 ≤ N := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hM2 : (d : ℝ) / 2 + 2 < m := by linarith
  have hb0 := eqtrace_b_nonneg (d := d) hs0 hN1
  have hstat := MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ S hN P X₀ W X hX
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le r) le_rfl
  have hfm : Measurable (fun x : Config d N => traceMaj m β⁻¹ ρβ x) := measurable_traceMaj hM2 hq hρc hN1
  have hYm : Measurable (fun p : ℝ × Ω => X (min S p.1).toNNReal p.2) :=
    HRS.MD.EQRem.eqrem_joint_meas ℱ S X hF.progressive
  have hbd : ∀ u : ℝ≥0, (u : ℝ) ≤ S →
      ∫⁻ ω, traceMaj m β⁻¹ ρβ (X u ω) ^ 2 ∂P ≤ ENNReal.ofReal ((C₀ * bracketBias d s N) ^ 2) := by
    intro u hu
    calc ∫⁻ ω, traceMaj m β⁻¹ ρβ (X u ω) ^ 2 ∂P
        = ∫⁻ x, traceMaj m β⁻¹ ρβ x ^ 2 ∂(P.map (X u)) :=
          (lintegral_map (hfm.pow_const 2) (hXm _)).symm
      _ ≤ _ := by rw [hstat u hu]; exact hk β hβI ρβ hρ N hN
  obtain ⟨hmeas, hL2⟩ := ret_b3_core P S hS X (fun x => traceMaj m β⁻¹ ρβ x) hfm hYm hXm _ hbd
  refine ⟨hmeas, ?_, ?_⟩
  · intro ω
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [min_eq_right hr.2]
    exact traceNorm_le_maj hd hm hq hρc hρp hN1 _
  · refine hL2.trans ?_
    have hu : 0 ≤ C₀ * bracketBias d s N := mul_nonneg hC₀.le hb0
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hS]
    refine ENNReal.ofReal_le_ofReal ?_
    calc S * ((C₀ * bracketBias d s N) ^ 2 * S) = (S * (C₀ * bracketBias d s N)) ^ 2 := by ring
      _ ≤ ((S + 1) * (C₀ * bracketBias d s N)) ^ 2 := by
          apply pow_le_pow_left₀ (mul_nonneg hS hu)
          nlinarith
      _ = _ := by ring

end HRS.ME.Ret

end
