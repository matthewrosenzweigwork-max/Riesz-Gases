import HRS.MC.E213U12c
import HRS.MC.S7FCF5GE1

/-!
# Packet e213u12 (part d): the far estimate for the particle covariance term, and `far_particle_proof`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U12

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u12_J_prob (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (N : ℕ), 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      PreparedRealization (regime S β₀ hE).D P
        (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
          (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (farCoef (max (a - Rw) 0) (fun v => etaE m (X v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂P| ≤ K * Real.exp (-c * Rw) := by
  obtain ⟨C₂, c, hC₂, hc, hJ⟩ := u12_J_far_bound hE T hT
  obtain ⟨Ce, hCe⟩ := HRS.MC.Sec7.S7FCF5O.fcf5_D2_Shat_moment_proof (regime S β₀ hE) (rLvl d) rfl 1 one_pos 1 le_rfl
  have hCm : 0 ≤ max Ce 0 := le_max_right _ _
  refine ⟨C₂ * max Ce 0 / c + 1, c, by positivity, hc, ?_⟩
  intro N hN Ω _ P _ X₀ W X hreal a ha Rw hRw Φ hΦ
  have hN1 : 1 ≤ N := by omega
  have hH0 : 0 < a + T := by linarith
  have hH : a < a + T := by linarith
  have hb0 : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hS := hreal.solution 0
  have hd : (d : ℝ) < 2 * rLvl d := by
    unfold rLvl
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdens : ∀ s : ℝ, 0 ≤ s → IsProbDensity ((regime S β₀ hE).ρ s) := fun s hs =>
    ((regime S β₀ hE).mf (s + 1) (by linarith)).density s ⟨hs, by linarith⟩
  -- the process `u` (clamped to `t ≥ 0`)
  set u : ℝ → Ω → NegSobolev d (rLvl d) := fun t ω =>
    etaE (rLvl d) (X (max t 0).toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ (max t 0))) with hu
  have hum : ∀ t, Measurable (u t) := by
    intro t
    haveI := isProb_withDensityReal (hdens (max t 0) (le_max_right _ _))
    exact ((measurable_ofMeasureDiff_empirical hd (withDensityReal ((regime S β₀ hE).ρ (max t 0))) hN1).comp
      (hS.adapted (max t 0).toNNReal)).const_smul (Real.sqrt N)
  have huc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [(HRS.MC.Sec7.S7FCF5G.fcf5_E1_window_cont_proof (regime S β₀ hE) (rLvl d) rfl (a + T) hN1 P X₀ W X
      hreal 0 le_rfl).1] with ω hω
    rw [continuousOn_iff_continuous_restrict]
    refine hω.congr (fun t => ?_)
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    simp only [Set.restrict_apply, hu, zero_add, max_eq_left ht]
  obtain ⟨Fe, hFe, N0, hN0m, hN0, hFeeq⟩ := HRS.MC.Sec7.S7FCW12.s7fcw12_caratheodory P hH0.le u hum huc 0
  have hFm : ∀ ω, Measurable (fun v => Fe v ω) := fun ω => hFe.comp (measurable_id.prodMk measurable_const)
  have hbound := u12_final_bound P
    (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
      (farCoef (max (a - Rw) 0) (fun v => etaE m (X v.toNNReal ω)
        (withDensityReal ((regime S β₀ hE).ρ v))))) Fe hFe (a + T) a Rw c C₂ (max Ce 0) hc hC₂.le hCm
    ha hRw hH ?_ ?_
  · refine hbound.trans ?_
    have h1 : C₂ * max Ce 0 * (Real.exp (-c * Rw) / c) = C₂ * max Ce 0 / c * Real.exp (-c * Rw) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · intro v hv
    calc ∫⁻ ω, ‖Fe v ω‖ₑ ∂P
        = ∫⁻ ω, ‖u v ω‖ₑ ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
          rw [hFeeq ω hω v hv]
      _ ≤ ∫⁻ ω, HRS.MC.Sec7.FCF5Plan.fcf5Shat (regime S β₀ hE) (rLvl d) v 1 X ω ^ (1 : ℝ) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [ENNReal.rpow_one]
          have hmax : max v 0 = v := max_eq_left hv.1
          have := HRS.MC.Sec7.S7FCF5R.S7FCF5R_etaE_le_Shat (regime S β₀ hE) (rLvl d) 1 v X ω v
            ⟨0, ⟨by simp, by simp⟩, by simp⟩
          simpa only [hu, hmax] using this
      _ ≤ ENNReal.ofReal Ce := hCe N hN P X₀ W X hreal v hv.1
      _ ≤ ENNReal.ofReal (max Ce 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, huc] with ω hω hωc hfin
    have hbm : Measurable (nearCoef 0 (fun v => Fe v ω)) := u12_nearCoef_meas _ (hFm ω)
    have hcont : ContinuousOn (fun v => Fe v ω) (Set.Icc 0 (a + T)) :=
      hωc.congr (fun v hv => hFeeq ω hω v hv)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a + T)).exists_bound_of_continuousOn hcont
    refine hJ a ha Φ hΦ _ (fun v => Fe v ω) hbm M hM _ (fun v hv => ?_) _ hb0 hba
    show etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)) = NegSobolev.embed m (Fe v ω)
    haveI := isProb_withDensityReal (hdens v hv.1.le)
    haveI : IsProbabilityMeasure (Measure.dirac (X v.toNNReal ω)) := inferInstance
    rw [(HRS.MC.E213U6.etaE_zetaE_embed_proof hE (Measure.dirac (X v.toNNReal ω)) (X v.toNNReal ω)
      (withDensityReal ((regime S β₀ hE).ρ v))).1, hFeeq ω hω v ⟨hv.1.le, hv.2⟩]
    simp only [hu, max_eq_left hv.1.le]

/-- **Far window, particle system** (statement of `HRS.MC.E213Plan.far_particle`, verbatim). -/
theorem far_particle_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ), 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      PreparedRealization (regime S β₀ hE).D P
        (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
          (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (farCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
              (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) ∂P| +
        (1 / 2) * |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (farCoef (max (a - Rw) 0) (fun v => etaE m (X v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂P| ≤ C * Real.exp (-c * Rw) := by
  obtain ⟨K₁, c₁, hK₁, hc₁, h₁⟩ := u12_drift_prob hE T hT
  obtain ⟨K₂, c₂, hK₂, hc₂, h₂⟩ := u12_J_prob hE T hT
  refine ⟨K₁ + K₂, min c₁ c₂, by positivity, lt_min hc₁ hc₂, ?_⟩
  intro N hN Ω _ P _ X₀ W X hreal a ha Rw hRw Φ hΦ
  have e₁ : Real.exp (-c₁ * Rw) ≤ Real.exp (-(min c₁ c₂) * Rw) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c₁ c₂])
  have e₂ : Real.exp (-c₂ * Rw) ≤ Real.exp (-(min c₁ c₂) * Rw) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c₁ c₂])
  have b₁ := h₁ N hN P X₀ W X hreal a ha Rw hRw Φ hΦ
  have b₂ := h₂ N hN P X₀ W X hreal a ha Rw hRw Φ hΦ
  have p := Real.exp_pos (-(min c₁ c₂) * Rw)
  nlinarith [mul_le_mul_of_nonneg_left e₁ hK₁.le, mul_le_mul_of_nonneg_left e₂ hK₂.le, abs_nonneg
    (∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (farCoef (max (a - Rw) 0) (fun v => etaE m (X v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂P)]

end HRS.MC.E213U12

end
