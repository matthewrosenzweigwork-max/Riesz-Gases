import HRS.MD.EQBurnBurnEngine
import HRS.ME.RetWeight

/-!
# Row 5.10, packet R4: the weighted engine

The enlargement and the identification of the Gaussian window of `eqb_engine` are taken out (they enter as data and as the hypothesis
`hid`), and the measure `P₁` is replaced by the probability measure `P₁.withDensity w` in the application of `t25p_stage2`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem ret_engine_core_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    {K c T Cmax : ℝ} (hK : 0 < K) (hc : 0 < c) (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax Vev)
    (hdual : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    {Ω₁ : Type} [mΩ₁ : MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀ : Ω₁ → Config d N) (W : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X : ℝ≥0 → Ω₁ → Config d N)
    (hX : IsStationaryGibbsFlow P₁ s hs0 hsd V β hβ (a + T) X₀ W X)
    (ℱ₁ : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ)
    (hF : IsFilteredSolution P₁ ℱ₁ W'' W X)
    (X₀' : Ω₁ → NegSobolev d m) (hX₀' : Measurable[ℱ₁ 0] X₀')
    (w : Ω₁ → ℝ≥0∞) (hw : Measurable[ℱ₁ 0] w) {B : ℝ≥0} (hB : ∀ ω, w ω ≤ B)
    (h1 : ∫⁻ ω, w ω ∂P₁ = 1) [IsProbabilityMeasure (P₁.withDensity w)]
    (Λ : Measure (PathSp T (NegSobolev d m)))
    (hid : ∀ (Ω₂ : Type) [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (ℱ₂ : Filtration ℝ mΩ₂) (ξ : Ω₂ → NegSobolev d m) (G : ℝ → Ω₂ → NegSobolev d m),
      Measurable ξ →
      IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) G
        (fun r _ => HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r) →
      Indep (MeasurableSpace.comap ξ inferInstance)
        (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G τ) inferInstance) P₂ →
      P₂.map ξ = (P₁.withDensity w).map X₀' →
      ∀ Zb : ℝ → Ω₂ → NegSobolev d m,
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t)) →
        (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
        (∀ t, Measurable (Zb t)) →
        Λ = law P₂ (windowPath a T (fun t ω => Vev t 0 (ξ ω) + Zb t ω))) :
    ENNReal.ofReal (smoothDist 2
        (law (P₁.withDensity w) (windowPath a T (fun t ω => zetaE m (P₁.map (X t.toNNReal)) (X t.toNNReal ω)) :
          Ω₁ → PathSp T (NegSobolev d m))) Λ) ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) *
          ∫⁻ ω, w ω * ‖zetaE m (P₁.map (X 0)) (X 0 ω) - X₀' ω‖ₑ ∂P₁ +
        ∫⁻ ω, w ω * (⨆ t ∈ ratTimes a T,
          (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ X k t ω)) ^ (1 / 2 : ℝ)) ∂P₁ +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, w ω * (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
                covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁ := by
  classical
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmd2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hS : 0 < a + T := by linarith
  have htr := eqb_traj hd hs0 hsd V hV hβ ρβ hρβ
  have hPS : IsParticleSystem P₁ htr.dyn (a + T) X₀ W X := by
    refine ⟨hX.flow.brownian, hX.flow.indep, ?_⟩
    rcases hX.flow.flow with ⟨hsol, -⟩ | ⟨h1, -⟩
    · exact hsol
    · omega
  obtain ⟨Mart, hMart, hMid⟩ := HRS.AdjK.adjk_particle_martingale_proof hd htr m hmd (a + T) hS hN
    P₁ _ _ X hPS ℱ₁ W'' hF
  set Sg : ℝ → Ω₁ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) :=
    fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω)) with hSg
  obtain ⟨Z₁, hZ₁S, hZ₁c, hZ₁m⟩ := hEv.exists_conv (a + T) hS Ω₁ P₁ ℱ₁ Mart Sg hMart
  obtain ⟨Zm, hZmm, hZmc, hZmeq⟩ := HRS.GF.gf_measurable_modification_proof P₁ (a + T) Z₁ hZ₁c hZ₁m
  have hZmS : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv P₁ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Zm t) :=
    fun t ht => HRS.GF.isStochConv_congr_ae (hZ₁S t ht) (hZmeq t ht).symm
  have hZmae : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), AEMeasurable (Zm t) P₁ :=
    fun t _ => (hZmm t).aemeasurable
  have hZmcae : ∀ᵐ ω ∂P₁, ContinuousOn (fun t => Zm t ω) (Set.Icc 0 (a + T)) :=
    Filter.Eventually.of_forall hZmc
  have hmild := HRS.MD.EQMild.eq_mild_stationary_proof hd hs0 hsd V hV hβ ρβ hρβ m hmd (a + T) hS.le hN
    P₁ _ _ X hX ℱ₁ W'' hF Mart hMart hMid Vev hdual Zm hZmS hZmae hZmcae
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (a + T) hN P₁ _ _ X hX
  have hYm : ∀ t, Measurable (X t) := fun t => (hF.adapted t).mono (ℱ₁.le t) le_rfl
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hYc := (HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P₁ hX).2.2
  have hVc : ∀ x : NegSobolev d m, ContinuousOn (fun t : ℝ => Vev t 0 x) (Set.Icc 0 (a + T)) :=
    fun x => HRS.Uniform.Comp28.continuousOn_V_zero Vev (hEv.plain _ hS.le).2.2 x
  obtain ⟨hRm, hRc, hBm, hbd⟩ := eqb_rem_package hmd2 (by omega : 1 ≤ N) ha hT P₁ X
    (canonicalGibbs (periodicRiesz d s) V N β) hYm hstat hYc Vev hVc Zm hZmm hZmcae
    (fun k t ω => statForcingCoord d hs0 hsd V hβ ρβ X k t ω) hmild
  -- the change of measure
  have hac : P₁.withDensity w ≪ P₁ := withDensity_absolutelyContinuous P₁ w
  have hwm : Measurable w := hw.mono (ℱ₁.le 0) le_rfl
  have hMartw : IsHilbertMartingaleWithCovariation (P₁.withDensity w) ℱ₁ (a + T) Mart Sg :=
    isHilbertMartingale_withDensity P₁ hMart hw hB h1
  have hZmSw : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv (P₁.withDensity w) Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Zm t) :=
    fun t ht => isStochConv_withDensity P₁ (hZmS t ht) hB hwm
  have hZmcw : ∀ᵐ ω ∂(P₁.withDensity w), ContinuousOn (fun t => Zm t ω) (Set.Icc 0 (a + T)) :=
    hac.ae_le hZmcae
  have hRcw := hac.ae_le hRc
  have hbdw := hac.ae_le hbd
  -- the engine
  obtain ⟨C, hC0, hmain⟩ := t25p_stage2 hK.le hc.le hT Vev hEv
  have : IsProbabilityMeasure (P₁.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hX0meas : Measurable[ℱ₁ 0] (fun ω => zetaE m (P₁.map (X 0)) (X 0 ω)) :=
    (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable.comp (hF.adapted 0)
  have key := hmain a ha Ω₁ (P₁.withDensity w) ℱ₁ (fun ω => zetaE m (P₁.map (X 0)) (X 0 ω)) X₀'
    hX0meas hX₀' Mart Sg hMartw
    (HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ)) (t25p_detCov hd htr hmd hS)
    (fun r hr => t25p_covDensT_zero hr _) Zm
    (fun t ω => zetaE m (P₁.map (X t.toNNReal)) (X t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (X 0)) (X 0 ω)) - Zm t ω)
    (fun t ω => zetaE m (P₁.map (X t.toNNReal)) (X t.toNNReal ω))
    hZmSw hZmcw hZmm hRcw hRm (fun t _ ω => by abel) _ (hBm.mono_ac hac) hbdw Λ hid
  have hJ : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
      ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        traceNormForm (Sg r ω - HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r))) =
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ))) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp [HRS.GF.covDensT, hr, hSg]
  have hfin : ∀ᵐ ω ∂P₁, w ω < ∞ :=
    Filter.Eventually.of_forall fun ω => lt_of_le_of_lt (hB ω) ENNReal.coe_lt_top
  have hconv : ∀ g : Ω₁ → ℝ≥0∞, ∫⁻ ω, g ω ∂(P₁.withDensity w) = ∫⁻ ω, w ω * g ω ∂P₁ := fun g =>
    lintegral_withDensity_eq_lintegral_mul_non_measurable P₁ hwm hfin g
  obtain ⟨key1, -⟩ := key
  rw [hconv, hconv, hconv] at key1
  simp_rw [hJ] at key1
  exact key1

end HRS.ME.Ret

end
