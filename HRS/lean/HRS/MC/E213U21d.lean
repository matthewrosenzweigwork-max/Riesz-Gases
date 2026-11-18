import HRS.MC.E213U21c

/-!
# Packet e213u21 (part d): near/far splitting of the particle Riemann--Stieltjes integrals, almost surely

`u21_split_ae_A`, `u21_split_ae_J`: for a prepared realisation, a.s. in `ω`,
`rsA(whole) = rsA(near part) + rsA(far part)` (`rsJ` likewise), with the level-`m` coefficients
`quadFieldAt m …`, `etaE m …` of `window_identity`.  Proof: jointly measurable modifications of the coefficient
(`S7FCF5J_joint_modif`, `s7fcw12_caratheodory`), `rs_split_drift/J`, and the congruence lemmas `u12_rsA_congr`,
`u12_rsJ_congr` (only the values on `(0,a+T]` matter).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- A jointly measurable process with uniformly bounded `L¹(P)` norms has a.s. finite time-integral on `[0,H]`. -/
theorem u21_ae_lintegral_fin {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → E)
    (hF : Measurable (Function.uncurry F)) (H C : ℝ)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) H, ∫⁻ ω, ‖F v ω‖ₑ ∂P ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂P, ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ < ∞ := by
  have T2 := HRS.MC.E213U12.u12_tonelli P F hF H C hb (fun _ => 1) measurable_const (Set.Icc 0 H)
    measurableSet_Icc le_rfl
  simp only [one_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at T2
  have hmeasAll : Measurable (fun ω => ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ ∂volume) := by
    have : Measurable (fun p : Ω × ℝ => ‖F p.2 p.1‖ₑ) := (hF.comp measurable_swap).enorm
    exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) H))
  refine ae_lt_top hmeasAll ?_
  refine ne_top_of_le_ne_top ?_ T2
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)

section Particle

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u21_split_ae_A (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) :
    ∀ᵐ ω ∂P,
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) =
        rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
            (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) +
        rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (farCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
            (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) := by
  obtain ⟨Cb, hCb⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof (regime S β₀ hE) (rLvl d) rfl 1 le_rfl
  have hH0 : 0 < a + T := by linarith
  have hS := hreal.solution (a + T)
  obtain ⟨Fp, hFp, N0, hN0m, hN0, hFpeq⟩ := HRS.MC.Sec7.S7FCF5J.S7FCF5J_joint_modif (regime S β₀ hE) (rLvl d) 0
    (a + T) hH0 le_rfl P X hS.adapted hS.cont
  have hFm : ∀ ω, Measurable (fun v => Fp v ω) := fun ω => hFp.comp (measurable_id.prodMk measurable_const)
  have hfin := u21_ae_lintegral_fin P Fp hFp (a + T) (max Cb 0) (fun v hv => by
    calc ∫⁻ ω, ‖Fp v ω‖ₑ ∂P
        = ∫⁻ ω, ‖quadFieldAt (rLvl d) (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω‖ₑ ^
            (1 : ℝ) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
          rw [hFpeq ω hω v hv, zero_add, ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal Cb := hCb N hN P X₀ W X hreal v hv.1
      _ ≤ ENNReal.ofReal (max Cb 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _))
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hfin] with ω hω hωfin
  have hbm : Measurable (nearCoef 0 (fun v => Fp v ω)) := HRS.MC.E213U12.u12_nearCoef_meas _ (hFm ω)
  have hbi : IntegrableOn (fun v => ‖Fp v ω‖) (Set.Icc 0 (a + T)) :=
    HRS.MC.E213U12.u12_integrableOn_of_lintegral (fun v => Fp v ω) (hFm ω).aestronglyMeasurable _ hωfin
  obtain ⟨-, -, hsum⟩ := HRS.MC.E213U7.rs_split_drift_proof hE T hT a ha Φ hΦ (zetaWin m (a + T) 0 P X ω)
    (fun v => Fp v ω) hbm hbi b hb hba
  have hq : ∀ v ∈ Set.Ioc (0 : ℝ) (a + T), quadFieldAt m (regime S β₀ hE).D.s
      (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω = NegSobolev.embed m (Fp v ω) := by
    intro v hv
    rw [HRS.MC.E213U6.quadFieldAt_embed_proof hE N hN P X₀ W X hreal v hv.1.le ω,
      hFpeq ω hω v ⟨hv.1.le, hv.2⟩, zero_add]
  rw [HRS.MC.E213U12.u12_rsA_congr hE T hT a ha _ _ _ (fun v => NegSobolev.embed m (Fp v ω)) hq,
    HRS.MC.E213U12.u12_rsA_congr hE T hT a ha _ _
      (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω))
      (nearCoef b (fun v => NegSobolev.embed m (Fp v ω))) (fun v hv => by simp only [nearCoef, hq v hv]),
    HRS.MC.E213U12.u12_rsA_congr hE T hT a ha _ _
      (farCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω))
      (farCoef b (fun v => NegSobolev.embed m (Fp v ω))) (fun v hv => by simp only [farCoef, hq v hv])]
  exact hsum

theorem u21_split_ae_J (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) :
    ∀ᵐ ω ∂P,
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) =
        rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (nearCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)))) +
        rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
          (farCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)))) := by
  have hN1 : 1 ≤ N := by omega
  have hH0 : 0 < a + T := by linarith
  have hS := hreal.solution 0
  have hd : (d : ℝ) < 2 * rLvl d := by
    unfold rLvl
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdens : ∀ s : ℝ, 0 ≤ s → IsProbDensity ((regime S β₀ hE).ρ s) := fun s hs =>
    ((regime S β₀ hE).mf (s + 1) (by linarith)).density s ⟨hs, by linarith⟩
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
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, huc] with ω hω hωc
  have hbm : Measurable (nearCoef 0 (fun v => Fe v ω)) := HRS.MC.E213U12.u12_nearCoef_meas _ (hFm ω)
  have hcont : ContinuousOn (fun v => Fe v ω) (Set.Icc 0 (a + T)) :=
    hωc.congr (fun v hv => hFeeq ω hω v hv)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a + T)).exists_bound_of_continuousOn hcont
  obtain ⟨-, -, hsum⟩ := HRS.MC.E213U7.rs_split_J_proof hE T hT a ha Φ hΦ (zetaWin m (a + T) 0 P X ω)
    (fun v => Fe v ω) hbm M hM b hb hba
  have hq : ∀ v ∈ Set.Ioc (0 : ℝ) (a + T), etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)) =
      NegSobolev.embed m (Fe v ω) := by
    intro v hv
    haveI := isProb_withDensityReal (hdens v hv.1.le)
    haveI : IsProbabilityMeasure (Measure.dirac (X v.toNNReal ω)) := inferInstance
    rw [(HRS.MC.E213U6.etaE_zetaE_embed_proof hE (Measure.dirac (X v.toNNReal ω)) (X v.toNNReal ω)
      (withDensityReal ((regime S β₀ hE).ρ v))).1, hFeeq ω hω v ⟨hv.1.le, hv.2⟩]
    simp only [hu, max_eq_left hv.1.le]
  rw [HRS.MC.E213U12.u12_rsJ_congr hE T hT a ha _ _ _ (fun v => NegSobolev.embed m (Fe v ω)) hq,
    HRS.MC.E213U12.u12_rsJ_congr hE T hT a ha _ _
      (nearCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))))
      (nearCoef b (fun v => NegSobolev.embed m (Fe v ω))) (fun v hv => by simp only [nearCoef, hq v hv]),
    HRS.MC.E213U12.u12_rsJ_congr hE T hT a ha _ _
      (farCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))))
      (farCoef b (fun v => NegSobolev.embed m (Fe v ω))) (fun v hv => by simp only [farCoef, hq v hv])]
  exact hsum

end Particle

end HRS.MC.E213U21

end
