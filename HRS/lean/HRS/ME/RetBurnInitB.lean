import HRS.ME.RetEngine
import HRS.MD.EQBurnBurnMain
import HRS.MD.EQBurnWire
import HRS.Main.ThermLinFinal

/-!
# Row 5.10, packet B3 (part B): the linear solution and the remainder majorant

* `ret_b3_linear_exists`: a solution of the linear fluctuation equation with prescribed initial law for the stationary
  mean-field data `ρ^t ≡ ρβ`;
* `ret_b3_remMeas`: almost-everywhere measurability of the remainder majorant of the stationary flow (the construction of
  `HRS.ME.Ret.ret_engine_core_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

theorem ret_b3_linear_exists (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T)
    (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
      Measurable Y₀ ∧ P'.map Y₀ = ν ∧
      IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T Y₀ Y := by
  obtain ⟨hρs, -, -, -, -⟩ := HRS.MD.EQRem.eqrem_setup hd hs0 hsd V hV hβ hρβ
  let S : PreparedData d :=
    ⟨s, hs0, hsd, hd, β, hβ, V, hV, ρβ, hρs, fun _ => ρβ, rfl, fun K _ =>
      ⟨fun _ => PDE.coeffOf ρβ,
        HRS.Uniform.Q48b.q48b_isMFSolutionHK (by omega) s hs0 hsd β hβ V hV ρβ hρβ hρs.smooth hρs.pos K,
        HRS.Uniform.Q48b.q48b_mfPath_const ρβ hρs.smooth⟩⟩
  obtain ⟨Ω', mΩ', P', hP', Y₀, Y, hY⟩ := preparedLinear_exists_proof S m hm T hT ν
  exact ⟨Ω', mΩ', P', hP', Y₀, Y, hY.meas, hY.law_init, hY.sol⟩

set_option maxHeartbeats 1600000 in
theorem ret_b3_remMeas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    {K c T Cmax : ℝ} (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax Vev)
    (hdual : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    {Ω₁ : Type} [mΩ₁ : MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀ : Ω₁ → Config d N) (W : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X : ℝ≥0 → Ω₁ → Config d N)
    (hX : IsStationaryGibbsFlow P₁ s hs0 hsd V β hβ (a + T) X₀ W X)
    (ℱ₁ : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ)
    (hF : IsFilteredSolution P₁ ℱ₁ W'' W X) :
    AEMeasurable (fun ω => ⨆ t ∈ ratTimes a T,
      (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ X k t ω)) ^ (1 / 2 : ℝ)) P₁ := by
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
  obtain ⟨-, -, hBm, -⟩ := eqb_rem_package hmd2 (by omega : 1 ≤ N) ha hT P₁ X
    (canonicalGibbs (periodicRiesz d s) V N β) hYm hstat hYc Vev hVc Zm hZmm hZmcae
    (fun k t ω => statForcingCoord d hs0 hsd V hβ ρβ X k t ω) hmild
  exact hBm

end HRS.ME.Ret

end
