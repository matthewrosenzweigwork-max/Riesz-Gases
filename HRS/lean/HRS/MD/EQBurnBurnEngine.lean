import HRS.MD.EQBurnBurnRem
import HRS.MD.EQBurnBurnLaw
import HRS.MD.EQBurnGaussLinMain
import HRS.MD.EQBurnEnlarge
import HRS.Main.T25PAux23
import HRS.Main.T25PAux13
import HRS.Main.T25PAux19
import HRS.Sections.AdjKCFinal

/-!
# EQ-BURN P4, part 6: application of the engine `t25p_stage2`

`eqb_engine`: for a stationary Gibbs flow `X` on `(Ω,P)` and a stationary Gaussian field `Z` on `(Ω',P')`, an enlarged space `(Ω₁,P₁)`
with a measure preserving projection `π`, a filtered stationary Gibbs flow `X ∘ π` and an `ℱ₁ 0`-measurable `η'` with law `law (Z 0)` such
that the two comparison inequalities of `t25p_stage2` hold, with the explicit terms (initial term, remainder majorant `Bm`, trace term).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29

variable {d : ℕ}

/-- The stationary trajectory `ρ^t ≡ ρβ`. -/
theorem eqb_traj (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    IsSmoothPositiveTrajectory d s β V ρβ (fun _ => ρβ) := by
  obtain ⟨hρs, -, -, -, -⟩ := HRS.MD.EQRem.eqrem_setup hd hs0 hsd V hV hβ hρβ
  refine ⟨hs0, hsd, hβ, hV, hρs, fun K _ => ⟨fun _ => PDE.coeffOf ρβ, ?_, fun t _ => ?_⟩⟩
  · exact HRS.Uniform.Q48b.q48b_isMFSolutionHK (by omega) s hs0 hsd β hβ V hV ρβ hρβ hρs.smooth
      hρs.pos K
  · exact congrFun (HRS.Uniform.Q48b.q48b_mfPath_const ρβ hρs.smooth) t

set_option maxHeartbeats 1600000 in
theorem eqb_engine (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    {K c T Cmax : ℝ} (hK : 0 < K) (hc : 0 < c) (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax Vev)
    (hdual : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (π : Ω₁ → Ω) (_ : MeasurePreserving π P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
      (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ) (η' : Ω₁ → NegSobolev d m),
      IsStationaryGibbsFlow P₁ s hs0 hsd V β hβ (a + T) (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      IsFilteredSolution P₁ ℱ₁ W'' (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) ∧
      Measurable η' ∧ P₁.map η' = P'.map (Z 0) ∧
      (ENNReal.ofReal (smoothDist 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z))) ≤
        ENNReal.ofReal (K * Real.exp (-c * a)) *
          ∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ∂P₁ +
        ∫⁻ ω, (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ
            (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ∂P₁ +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
                covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ∧
      (∀ p : ℝ, (p = 1 ∨ p = 2) →
        wassersteinE p (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal ((2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) * Real.exp (-c * a)) *
              (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) +
            (∫⁻ ω, (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ
                (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ^ p ∂P₁) ^ (1 / p) +
            ENNReal.ofReal (2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
                ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
                  traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
                    covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^ (1 / 2 : ℝ)) := by
  classical
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmd2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hS : 0 < a + T := by linarith
  have htr := eqb_traj hd hs0 hsd V hV hβ ρβ hρβ
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  haveI hν₀ : IsProbabilityMeasure (P'.map (Z 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hZ.meas 0).aemeasurable).2 inferInstance
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hℱπ, hη'0, hη'law⟩ :=
    HRS.MD.EQBurnEnlarge.eq_enlarge_proof hd hs0 hsd V hV hβ m (a + T) hS.le hN P X₀ W X hX ℱ W' hF
      (P'.map (Z 0))
  have hη'm : Measurable η' := hη'0.mono (ℱ₁.le 0) le_rfl
  have hη'map : P₁.map η' = P'.map (Z 0) := by
    have hX₀m : Measurable X₀ := hX.flow.init_meas
    have hpair : Measurable (fun ω' => (X₀ (π ω'), η' ω')) := (hX₀m.comp hπ.measurable).prodMk hη'm
    have h1 := Measure.map_map (μ := P₁) (measurable_snd (α := Config d N) (β := NegSobolev d m)) hpair
    rw [hη'law, Measure.map_snd_prod] at h1
    have h2 : (P.map X₀) Set.univ = 1 := by
      rw [Measure.map_apply hX₀m MeasurableSet.univ]; simp
    rw [h2, one_smul] at h1
    exact h1.symm
  -- the enlarged flow
  set X' : ℝ≥0 → Ω₁ → Config d N := fun t ω' => X t (π ω') with hX'def
  have hPS : IsParticleSystem P₁ htr.dyn (a + T) (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω')) X' := by
    refine ⟨hX'.flow.brownian, hX'.flow.indep, ?_⟩
    rcases hX'.flow.flow with ⟨hsol, -⟩ | ⟨h1, -⟩
    · exact hsol
    · omega
  obtain ⟨Mart, hMart, hMid⟩ := HRS.AdjK.adjk_particle_martingale_proof hd htr m hmd (a + T) hS hN
    P₁ _ _ X' hPS ℱ₁ W'' hF'
  set Sg : ℝ → Ω₁ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) :=
    fun r ω => covForm m β⁻¹ (empirical (X' r.toNNReal ω)) with hSg
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
    P₁ _ _ X' hX' ℱ₁ W'' hF' Mart hMart hMid Vev hdual Zm hZmS hZmae hZmcae
  -- stationarity and the remainder package
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (a + T) hN P₁ _ _ X' hX'
  have hYm : ∀ t, Measurable (X' t) := fun t => (hF'.adapted t).mono (ℱ₁.le t) le_rfl
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hYc := (EQInterp.flow_facts hd hs0 hsd V hV hβ hN P₁ hX').2.2
  have hVc : ∀ x : NegSobolev d m, ContinuousOn (fun t : ℝ => Vev t 0 x) (Set.Icc 0 (a + T)) :=
    fun x => HRS.Uniform.Comp28.continuousOn_V_zero Vev (hEv.plain _ hS.le).2.2 x
  obtain ⟨hRm, hRc, hBm, hbd⟩ := eqb_rem_package hmd2 (by omega : 1 ≤ N) ha hT P₁ X'
    (canonicalGibbs (periodicRiesz d s) V N β) hYm hstat hYc Vev hVc Zm hZmm hZmcae
    (fun k t ω => statForcingCoord d hs0 hsd V hβ ρβ X' k t ω) hmild
  -- the engine
  obtain ⟨C, hC0, hmain⟩ := t25p_stage2 hK.le hc.le hT Vev hEv
  have : IsProbabilityMeasure (P₁.map (X' 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hX0meas : Measurable[ℱ₁ 0] (fun ω => zetaE m (P₁.map (X' 0)) (X' 0 ω)) :=
    (EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable.comp (hF'.adapted 0)
  have hlin := HRS.MD.EQBurnGaussLin.eq_gauss_lin_proof hd hs0 hsd V hV hβ ρβ hρβ m hm (a + T) hS.le
    P' Z hZ
  have hid0 := t25p_hid hd htr hmd hT ha hK hc hdual hEv P' (Z 0) (hZ.meas 0) Z hlin (P'.map (Z 0)) rfl
    (law P' (Main.windowPath m T a Z)) rfl
  have key := hmain a ha Ω₁ P₁ ℱ₁ (fun ω => zetaE m (P₁.map (X' 0)) (X' 0 ω)) η' hX0meas hη'0 Mart Sg hMart
    (HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ)) (t25p_detCov hd htr hmd hS)
    (fun r hr => t25p_covDensT_zero hr _) Zm
    (fun t ω => zetaE m (P₁.map (X' t.toNNReal)) (X' t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (X' 0)) (X' 0 ω)) - Zm t ω)
    (fun t ω => zetaE m (P₁.map (X' t.toNNReal)) (X' t.toNNReal ω))
    hZmS hZmcae hZmm hRc hRm (fun t _ ω => by abel) _ hBm hbd
    (law P' (Main.windowPath m T a Z)) (by
      intro Ω₂ _ P₂ _ ℱ₂ ξ G hξ hG hind hlaw Zb h1 h2 h3
      exact hid0 Ω₂ P₂ ℱ₂ ξ G hξ hG hind (hlaw.trans hη'map) Zb h1 h2 h3)
  have hlawX : law P₁ (Uniform.windowPath a T (fun t ω' => zetaE m (P₁.map (fun ω'' => X t.toNNReal (π ω'')))
        (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)) =
      (law P (Main.windowZeta m T a P X) : Measure (PathSp T (NegSobolev d m))) :=
    eqb_law_windowZeta hd hs0 hsd V hV hβ hN ha hT.le P P₁ hπ hX hmd2
  have hlawZ : (law P' (Main.windowPath m T a Z) : Measure (PathSp T (NegSobolev d m))) =
      (law P' (Main.windowPath m T 0 Z) : Measure (PathSp T (NegSobolev d m))) :=
    eqb_gauss_window hd hs0 hsd V hβ ρβ m T hT.le P' Z hZ ha
  have hJ : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
      ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        traceNormForm (Sg r ω - HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r))) =
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
            covForm m β⁻¹ (withDensityReal ρβ))) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp [HRS.GF.covDensT, hr, hSg, hX'def]
  have hJint : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
      ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        traceNormForm (Sg r ω - HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r))) ∂P₁) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
            covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁ := lintegral_congr hJ
  obtain ⟨key1, key2⟩ := key
  rw [hlawX, hlawZ, hJint] at key1
  refine ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hη'm, hη'map, key1, ?_⟩
  intro p hp
  have := key2 p hp
  rw [hlawX, hlawZ, hJint] at this
  exact this

end HRS.MD.EQBurnBurn

end
