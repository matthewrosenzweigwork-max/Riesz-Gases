import HRS.MC.E213U12b
import HRS.MC.S7FCF5JB
import HRS.MC.S7FCF5IE2
import HRS.MC.S7FCF5OD2
import HRS.MC.S7FCF5RPath

/-!
# Packet e213u12 (part c): the far estimates for the particle system, drift and covariance parts

* `u12_drift_prob`: `|E rsA(far part of ℬ_N)| ≤ K e^{-c Rw}` from `u12_drift_far_bound`, the jointly measurable modification
  of `ℬ_N` (`S7FCF5J_joint_modif`) and the per-time moment bound `fcf5_F6a_B_section_moment_proof`.
* `u12_J_prob`: `|E rsJ(far part of η_N)| ≤ K e^{-c Rw}` from `u12_J_far_bound`, a jointly measurable modification of `η_N`
  (`s7fcw12_caratheodory`, continuity from E1) and the per-time moment bound of `η_N^v` by the window supremum
  `fcf5Shat` on the unit window `[v,v+1]` (`fcf5_D2_Shat_moment_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U12

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

theorem u12_nearCoef_meas {E : Type*} [MeasurableSpace E] [Zero E] (f : ℝ → E) (hf : Measurable f) :
    Measurable (nearCoef 0 f) := by
  unfold nearCoef
  exact Measurable.ite measurableSet_Ici hf measurable_const

theorem u12_integrableOn_of_lintegral {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : AEStronglyMeasurable f volume)
    (s : Set ℝ) (h : ∫⁻ v in s, ‖f v‖ₑ < ∞) : IntegrableOn (fun v => ‖f v‖) s := by
  refine ⟨hf.norm.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_norm] using h

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u12_drift_prob (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (N : ℕ), 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      PreparedRealization (regime S β₀ hE).D P
        (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
          (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (farCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
              (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) ∂P| ≤ K * Real.exp (-c * Rw) := by
  obtain ⟨C₁, c, hC₁, hc, hD⟩ := u12_drift_far_bound hE T hT
  obtain ⟨Cb, hCb⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof (regime S β₀ hE) (rLvl d) rfl 1 le_rfl
  have hCm : 0 ≤ max Cb 0 := le_max_right _ _
  refine ⟨C₁ * max Cb 0 / c + 1, c, by positivity, hc, ?_⟩
  intro N hN Ω _ P _ X₀ W X hreal a ha Rw hRw Φ hΦ
  have hH0 : 0 < a + T := by linarith
  have hH : a < a + T := by linarith
  have hb0 : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hS := hreal.solution (a + T)
  obtain ⟨Fp, hFp, N0, hN0m, hN0, hFpeq⟩ := HRS.MC.Sec7.S7FCF5J.S7FCF5J_joint_modif (regime S β₀ hE) (rLvl d) 0
    (a + T) hH0 le_rfl P X hS.adapted hS.cont
  have hFm : ∀ ω, Measurable (fun v => Fp v ω) := fun ω => hFp.comp (measurable_id.prodMk measurable_const)
  have hbound := u12_final_bound P
    (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
      (farCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω))) Fp hFp (a + T) a Rw c C₁ (max Cb 0) hc hC₁.le hCm
    ha hRw hH ?_ ?_
  · refine hbound.trans ?_
    have h1 : C₁ * max Cb 0 * (Real.exp (-c * Rw) / c) = C₁ * max Cb 0 / c * Real.exp (-c * Rw) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · intro v hv
    calc ∫⁻ ω, ‖Fp v ω‖ₑ ∂P
        = ∫⁻ ω, ‖quadFieldAt (rLvl d) (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω‖ₑ ^
            (1 : ℝ) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
          rw [hFpeq ω hω v hv, zero_add, ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal Cb := hCb N hN P X₀ W X hreal v hv.1
      _ ≤ ENNReal.ofReal (max Cb 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω hfin
    have hbm : Measurable (nearCoef 0 (fun v => Fp v ω)) := u12_nearCoef_meas _ (hFm ω)
    have hbi : IntegrableOn (fun v => ‖Fp v ω‖) (Set.Icc 0 (a + T)) :=
      u12_integrableOn_of_lintegral (fun v => Fp v ω) (hFm ω).aestronglyMeasurable _ hfin
    refine hD a ha Φ hΦ _ (fun v => Fp v ω) hbm hbi _ (fun v hv => ?_) _ hb0 hba
    show quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω =
      NegSobolev.embed m (Fp v ω)
    rw [HRS.MC.E213U6.quadFieldAt_embed_proof hE N hN P X₀ W X hreal v hv.1.le ω,
      hFpeq ω hω v ⟨hv.1.le, hv.2⟩, zero_add]

end HRS.MC.E213U12

end
