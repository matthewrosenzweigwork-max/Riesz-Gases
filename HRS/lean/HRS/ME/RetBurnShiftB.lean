import HRS.ME.RetEngine

/-!
# Row 5.10, shifted burn-in, part B: measurability of the remainder majorant

The majorant `Bm = sup_{t ∈ ratTimes a T} (coordEnergy …)^{1/2}` of the weighted engine is a.e. measurable (this is part of the
output of `eqb_rem_package`, not of the statement of `ret_engine_core_proof`, so the preamble of the engine is repeated).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem rbs_Bm_aemeas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
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
    (hF : IsFilteredSolution P₁ ℱ₁ W'' W X) :
    AEMeasurable (fun ω => ⨆ t ∈ ratTimes a T,
        (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ X k t ω)) ^ (1 / 2 : ℝ)) P₁ ∧
    Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ)))) := by
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
  refine ⟨hBm, ?_⟩
  have hmeasD : ∀ x y : NegSobolev d m, Measurable (fun p : Ω₁ × ℝ =>
      (Sg p.2 p.1 - covForm m β⁻¹ (withDensityReal ρβ)) x y) := fun x y => by
    simp only [ContinuousLinearMap.sub_apply]
    exact ((hMart.sigma_meas x y).comp measurable_swap).sub measurable_const
  have h1 := measurable_traceNormForm (H := NegSobolev d m) (α := Ω₁ × ℝ)
    (fun p => Sg p.2 p.1 - covForm m β⁻¹ (withDensityReal ρβ)) hmeasD
  have h3 : Measurable (fun p : Ω₁ × ℝ => Real.exp (-c * max (a - p.2) 0) ^ 2) :=
    (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_const.sub measurable_snd).max measurable_const))).pow_const 2
  have h2 : Measurable fun p : Ω₁ × ℝ => ENNReal.ofReal (Real.exp (-c * max (a - p.2) 0) ^ 2 *
      traceNormForm (Sg p.2 p.1 - covForm m β⁻¹ (withDensityReal ρβ))) :=
    ENNReal.measurable_ofReal.comp (h3.mul h1)
  exact h2.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) (a + T)))

end HRS.ME.Ret

end
