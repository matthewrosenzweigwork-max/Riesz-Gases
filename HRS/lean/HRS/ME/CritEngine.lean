import HRS.ME.CritStage2
import HRS.ME.CritSpec
import HRS.MD.EQBurnBurnEngine

/-!
# Critical engine (proof of `HRS.ME.Crit.crit_engine`)

Body of `HRS.MD.EQBurnBurn.eqb_engine` with the last step changed: the comparison `t25p_stage2` is replaced by its
`p = 2` critical version `HRS.ME.CritStage2.crit_stage2_proof` (Bures cost `bures2 (Sg r ω) (Cb r)`).  The conclusion is the
single `W_2` inequality with the initial term, the remainder majorant `Bm` and the Bures cost of the empirical covariance.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritEngine

open HRS HRS.MD HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

set_option maxHeartbeats 1600000 in
theorem crit_engine_proof {d : ℕ} : type_of% (@HRS.ME.Crit.crit_engine d) := by
  classical
  intro hd s hs0 hsd V hV β hβ ρβ hρβ m hm K c T Cmax hK hc hT Vev hEv hdual a ha N hN
    Ω mΩ P _ X₀ W X hX Ω' _ P' _ Z hZ
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
  obtain ⟨C, hC0, hmain⟩ := HRS.ME.CritStage2.crit_stage2_proof hK.le hc.le hT Vev hEv
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
        bures2 (Sg r ω) (HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r))) =
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ))) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp [HRS.GF.covDensT, hr, hSg, hX'def]
  have hJint : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
      ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (Sg r ω) (HRS.GF.covDensT m β⁻¹ (a + T) (fun _ => ρβ) r))) ∂P₁) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁ :=
    lintegral_congr hJ
  rw [hlawX, hlawZ, hJint] at key
  exact ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hη'm, hη'map, key⟩

end HRS.ME.CritEngine

end
