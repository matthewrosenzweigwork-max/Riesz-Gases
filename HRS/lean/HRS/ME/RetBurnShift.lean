import HRS.ME.RetBurnShiftA
import HRS.ME.RetBurnShiftB
import HRS.ME.RetBurnShiftC
import HRS.ME.RetBurnStmt
import HRS.ME.RetEngine
import HRS.MD.EQBurnBurnMain
import HRS.MD.EQEvoFinal
import HRS.MD.EQBurnDefs

/-!
# Row 5.10: the weighted burn-in estimate `RetBurnShift`

Route of `HRS.MD.EQBurnBurn.eq_burnin_of_evo_proof` with the weight `w = h (X 0 ∘ π)` on the enlarged space (an `ℱ₁ 0`-measurable
function): the enlargement, the particle martingale, the mild identity and `t25p_stage2` are in `ret_engine_core_proof`; the three terms
are bounded by Cauchy-Schwarz against `w`, with the `L²` bounds of the initial term (`EQInit`), the remainder (`eq_rem_integrated_proof`)
and the trace discrepancy (`rbs_trace_L2`).  The law of the window is identified with the pushforward of `P.withDensity (h ∘ X₀)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurn HRS.MD.EQBurnBurn

theorem rbs_ofReal_comm {x y : ℝ} (hx : 0 ≤ x) (L : ℝ≥0∞) :
    ENNReal.ofReal x * (L * ENNReal.ofReal y) = L * ENNReal.ofReal (x * y) := by
  rw [ENNReal.ofReal_mul hx]; ring

/-- The uniform evolution output (single `β`) as an evolution package; see `eqbw_evoPkg`. -/
theorem rbs_evoPkg {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ EvoPkg d s hs0 hsd V βm βp hβm m K c T Cmax := by
  obtain ⟨K, c, Cmax, hK, hc, hCmax, h⟩ :=
    HRS.MD.EQEvoFinal.eq_evolution_uniform_proof hd hs0 hsd V hV βm βp hβm hββ m T hT
  refine ⟨K, c, Cmax, hK, hc, hCmax, ?_⟩
  intro β hβ ρβ hρ
  obtain ⟨Vev, hdual, hplain, hdec, hmax, hconv⟩ := h β hβ ρβ hρ
  refine ⟨Vev, ⟨hplain, hdec, ?_, ?_⟩, hdual⟩
  · intro Ω mΩ P _ ℱ a ha M Sg hM Z hZS hZc hZm
    exact hmax Ω P ℱ a ha M Sg hM Z (fun t _ => (hZm t).aemeasurable) hZS hZc
  · intro T' hT' Ω mΩ P _ ℱ M Sg hM
    exact hconv T' hT'.le Ω P ℱ M Sg hM

set_option maxHeartbeats 3200000 in
theorem ret_burn_shift_proof (d : ℕ) : RetBurnShift d := by
  classical
  intro hd s hs0 hsd V hV β hβ m hm T hT
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hm1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmh : (d : ℝ) / 2 < m := by linarith
  have hmd2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨K, c, Cmax, hK, hc, hCmax, hevo⟩ :=
    rbs_evoPkg (d := d) hd hs0 hsd V hV β β hβ le_rfl m T hT.le
  set K' : ℝ := max K 1 with hK'def
  have hK'0 : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Crem, hCrem0, hrem⟩ := HRS.MD.EQRem.eq_rem_integrated_proof hd hs0 hsd V hV β β hβ le_rfl m hmd T hT.le
    K' c hK'0.le hc
  obtain ⟨Ct, hCt0, htr⟩ := rbs_trace_L2 hd hs0 hsd V hV hβ m hm1 hc hT.le
  obtain ⟨Cp, hCp0, hinp⟩ := HRS.MD.EQInit.eq_init_particle_proof hd hs0 hsd V hV β β hβ le_rfl m hmh
  obtain ⟨Cg, hCg0, hing⟩ := HRS.MD.EQInit.eq_init_gauss_proof hd hs0 hsd V hV β β hβ le_rfl m hmh
  set S0 : ℝ := Real.sqrt Cp + Real.sqrt Cg with hS0def
  have hS00 : 0 ≤ S0 := by positivity
  set μT : ℝ := 1 / (2 * c) + T with hμT
  have hμT0 : 0 ≤ μT := by positivity
  set C : ℝ := max (K' * S0) (Real.sqrt Crem + K' ^ 2 * (μT * Ct)) + 1 with hCdef
  have hC1 : K' * S0 ≤ C := by
    have := le_max_left (K' * S0) (Real.sqrt Crem + K' ^ 2 * (μT * Ct)); linarith
  have hC2 : Real.sqrt Crem + K' ^ 2 * (μT * Ct) ≤ C := by
    have := le_max_right (K' * S0) (Real.sqrt Crem + K' ^ 2 * (μT * Ct)); linarith
  have hC0 : 0 < C := by
    have : 0 ≤ K' * S0 := by positivity
    have := le_max_left (K' * S0) (Real.sqrt Crem + K' ^ 2 * (μT * Ct)); linarith
  refine ⟨C, c, hC0, hc, ?_⟩
  intro ρβ hρβ a ha N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ h hhm hbd h1
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨Vev, hEv, hdual⟩ := hevo β ⟨le_rfl, le_rfl⟩ ρβ hρβ
  have hEv' := eqb_ev_max hEv
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K' * Real.exp (-c * (t - u)) := hEv'.decay
  have hS : 0 < a + T := by linarith
  have htraj := eqb_traj hd hs0 hsd V hV hβ ρβ hρβ
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  haveI hν₀ : IsProbabilityMeasure (P'.map (Z 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hZ.meas 0).aemeasurable).2 inferInstance
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', -, hη'0, hη'law⟩ :=
    HRS.MD.EQBurnEnlarge.eq_enlarge_proof hd hs0 hsd V hV hβ m (a + T) hS.le hN P X₀ W X hX ℱ W' hF
      (P'.map (Z 0))
  have hη'm : Measurable η' := hη'0.mono (ℱ₁.le 0) le_rfl
  -- the weight
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hF.adapted t).mono (ℱ.le t) le_rfl
  have hstr : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) (a + T) X₀ W X := by
    rcases hX.flow.flow with ⟨h', _⟩ | ⟨h1', _⟩
    · exact h'
    · exfalso; omega
  have hae : X 0 =ᵐ[P] X₀ := hstr.init
  have hX₀m : Measurable X₀ := hX.flow.init_meas
  set w : Ω₁ → ℝ≥0∞ := fun ω' => h (X 0 (π ω')) with hwdef
  have hwm0 : Measurable[ℱ₁ 0] w := hhm.comp (hF'.adapted 0)
  have hwm : Measurable w := hwm0.mono (ℱ₁.le 0) le_rfl
  have hw1 : ∫⁻ ω', w ω' ∂P₁ = 1 := by
    have := rbs_w_lintegral hπ (hXm 0) hae hhm id measurable_id
    simpa [hwdef] using this.trans h1
  haveI hwprob : IsProbabilityMeasure (P₁.withDensity w) :=
    isProbabilityMeasure_withDensity_of_lintegral_eq_one P₁ hwm hw1
  have hwB : ∀ ω', w ω' ≤ M := fun ω' => hM _
  have hw2 : ∫⁻ ω', w ω' ^ 2 ∂P₁ = ∫⁻ ω, h (X₀ ω) ^ 2 ∂P :=
    rbs_w_lintegral hπ (hXm 0) hae hhm (fun x => x ^ 2) (measurable_id.pow_const 2)
  have hweta : (P₁.withDensity w).map η' = P'.map (Z 0) :=
    rbs_w_map_eta hπ hX₀m (hXm 0) hae hhm h1 hη'm hη'law
  have hwπ : (P₁.withDensity w).map π = P.withDensity (fun ω => h (X₀ ω)) :=
    rbs_w_map_pi hπ (hXm 0) hae hhm
  -- the identification of the target
  have hlin := HRS.MD.EQBurnGaussLin.eq_gauss_lin_proof hd hs0 hsd V hV hβ ρβ hρβ m hm (a + T) hS.le P' Z hZ
  have hid0 := t25p_hid hd htraj hmd hT ha hK'0 hc hdual hEv' P' (Z 0) (hZ.meas 0) Z hlin (P'.map (Z 0)) rfl
    (law P' (Main.windowPath m T a Z)) rfl
  have hlawZ : (law P' (Main.windowPath m T a Z) : Measure (PathSp T (NegSobolev d m))) =
      (law P' (Main.windowPath m T 0 Z) : Measure (PathSp T (NegSobolev d m))) :=
    eqb_gauss_window hd hs0 hsd V hβ ρβ m T hT.le P' Z hZ ha
  -- the engine
  have key := ret_engine_core_proof hd hs0 hsd V hV hβ ρβ hρβ m hm hK'0 hc hT Vev hEv' hdual ha hN P₁
    (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) hX' ℱ₁ W'' hF' η' hη'0 w hwm0 hwB
    hw1 (law P' (Main.windowPath m T 0 Z))
    (by
      intro Ω₂ _ P₂ _ ℱ₂ ξ G hξ hG hind hlaw Zb h1 h2 h3
      exact hlawZ.symm.trans (hid0 Ω₂ P₂ ℱ₂ ξ G hξ hG hind (hlaw.trans hweta) Zb h1 h2 h3))
  -- the law of the window
  have hmapt : ∀ t : ℝ≥0, P₁.map (fun ω'' => X t (π ω'')) = P.map (X t) := by
    intro t
    rw [← hπ.map_eq, Measure.map_map (hXm t) hπ.measurable]
    rfl
  have hfun : (Uniform.windowPath a T (fun t ω' => zetaE m (P₁.map (fun ω'' => X t.toNNReal (π ω'')))
        (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)) =
      fun ω' => Main.windowZeta m T a P X (π ω') := by
    funext ω'
    have := eqb_windowPath_eq P₁ m T a (fun t ω'' => X t (π ω'')) ω'
    refine this.trans ?_
    show HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (P₁.map (fun ω'' => X (Real.toNNReal (a + τ)) (π ω'')))
          (X (Real.toNNReal (a + τ)) (π ω'))) =
      HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (P.map (X (Real.toNNReal (a + τ)))) (X (Real.toNNReal (a + τ)) (π ω')))
    congr 1
    funext τ
    rw [hmapt]
  have hwae := HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN ha hT.le P hX hmd2
  have hlawL : law (P₁.withDensity w) (Uniform.windowPath a T (fun t ω' => zetaE m
        (P₁.map (fun ω'' => X t.toNNReal (π ω''))) (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)) =
      (P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T a P X) := by
    rw [hfun]
    unfold law
    have hae' : AEMeasurable (Main.windowZeta m T a P X) ((P₁.withDensity w).map π) := by
      rw [hwπ]
      exact hwae.mono_ac (withDensity_absolutelyContinuous _ _)
    have := AEMeasurable.map_map_of_aemeasurable hae' hπ.measurable.aemeasurable
    rw [hwπ] at this
    exact this.symm
  -- stationarity on the enlarged space and the initial term
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (a + T) hN P₁ _ _ _ hX'
  have hYm : ∀ t : ℝ≥0, Measurable (fun ω' => X t (π ω')) := fun t =>
    (hF'.adapted t).mono (ℱ₁.le t) le_rfl
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hzm : Measurable (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) :=
    (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable
  have hmap0 : P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω'')) = canonicalGibbs (periodicRiesz d s) V N β :=
    hstat 0 (by simp; positivity)
  have hζ0m : Measurable (fun ω => zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))) := by
    rw [hmap0]; exact hzm.comp (hYm 0)
  have hI1 : ∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))‖ₑ ^ 2 ∂P₁ ≤
      ENNReal.ofReal Cp := by
    rw [hmap0]
    have := lintegral_map (μ := P₁) (f := fun x => ‖zetaE m (canonicalGibbs (periodicRiesz d s) V N β) x‖ₑ ^ 2)
      (g := fun ω' => X (0 : ℝ≥0) (π ω')) (hzm.enorm.pow_const 2) (hYm 0)
    rw [← this, hmap0]
    exact hinp β ⟨le_rfl, le_rfl⟩ ρβ hρβ N hN
  have hI2 : ∫⁻ ω, ‖η' ω‖ₑ ^ 2 ∂P₁ ≤ ENNReal.ofReal Cg := by
    have h1' := lintegral_map (μ := P₁) (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := η')
      (measurable_enorm.pow_const 2) hη'm
    have h2' := lintegral_map (μ := P') (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := Z 0)
      (measurable_enorm.pow_const 2) (hZ.meas 0)
    have hη'map : P₁.map η' = P'.map (Z 0) := by
      have hpair : Measurable (fun ω' => (X₀ (π ω'), η' ω')) := (hX₀m.comp hπ.measurable).prodMk hη'm
      have h1'' := Measure.map_map (μ := P₁) (measurable_snd (α := Config d N) (β := NegSobolev d m)) hpair
      rw [hη'law, Measure.map_snd_prod] at h1''
      have h2'' : (P.map X₀) Set.univ = 1 := by
        rw [Measure.map_apply hX₀m MeasurableSet.univ]; simp
      rw [h2'', one_smul] at h1''
      exact h1''.symm
    rw [← h1', hη'map, h2']
    exact hing β ⟨le_rfl, le_rfl⟩ ρβ hρβ P' Z hZ
  obtain ⟨-, hD2⟩ := eqb_init_diff P₁ _ η' hζ0m.aemeasurable hη'm.aemeasurable hCp0.le hCg0.le hI1 hI2
  simp_rw [ENNReal.rpow_two] at hD2
  -- the remainder term
  obtain ⟨-, -, hB2⟩ := hrem β ⟨le_rfl, le_rfl⟩ ρβ hρβ a ha N hN P₁ _ _ _ hX' Vev hdual hdec
  -- the trace term
  have hJ := htr ρβ hρβ a ha N hN P₁ _ _ _ hX' ℱ₁ W'' hF'
  -- measurability
  obtain ⟨hBmae, hJm⟩ := rbs_Bm_aemeas hd hs0 hsd V hV hβ ρβ hρβ m hm hK'0 hc hT Vev hEv' hdual ha hN P₁
    (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) hX' ℱ₁ W'' hF'
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
  have hb0 : 0 ≤ bracketBias d s N := HRS.MD.EQTrace.eqtrace_b_nonneg (d := d) hs0 (by omega)
  have hbb : bracketBias d s N ≤ 2 * Real.sqrt (deltaN d s N) :=
    bracketBias_le_sqrt_deltaN (by omega) hs0 hsd (by omega)
  have hexp0 : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
  have hsq0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  set L : ℝ≥0∞ := (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) with hL
  have hLw : (∫⁻ ω', w ω' ^ 2 ∂P₁) ^ (1 / 2 : ℝ) = L := by rw [hw2]
  have hμ0 : 0 ≤ μT * Ct * bracketBias d s N := by positivity
  -- the three bounds
  have hT1 : ∫⁻ ω, w ω * ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ∂P₁ ≤
      L * ENNReal.ofReal S0 := by
    have := rbs_holder P₁ (w := w) hwm.aemeasurable (hζ0m.sub hη'm).enorm.aemeasurable hD2
    rwa [hLw] at this
  have hT2 : ∫⁻ ω, w ω * (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ
      (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ∂P₁ ≤
      L * ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) := by
    have h2 := rbs_l2_le P₁ (fun ω => ⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ
          (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) (mul_nonneg hCrem0.le hδ0) hB2
    rw [Real.sqrt_mul hCrem0.le] at h2
    have := rbs_holder P₁ (w := w) hwm.aemeasurable hBmae h2
    rwa [hLw] at this
  have hT3 : ∫⁻ ω, w ω * (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
                covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁ ≤
      L * ENNReal.ofReal (μT * Ct * bracketBias d s N) := by
    have h2 := rbs_l2_le P₁ (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
                covForm m β⁻¹ (withDensityReal ρβ)))) (sq_nonneg _) hJ
    rw [Real.sqrt_sq hμ0] at h2
    have := rbs_holder P₁ (w := w) hwm.aemeasurable hJm.aemeasurable h2
    rwa [hLw] at this
  -- assembling
  calc ENNReal.ofReal (smoothDist 2 ((P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T a P X))
        (law P' (Main.windowPath m T 0 Z)))
      = ENNReal.ofReal (smoothDist 2 (law (P₁.withDensity w) (Uniform.windowPath a T (fun t ω' => zetaE m
        (P₁.map (fun ω'' => X t.toNNReal (π ω''))) (X t.toNNReal (π ω'))) : Ω₁ → PathSp T (NegSobolev d m)))
        (law P' (Main.windowPath m T 0 Z))) := by rw [hlawL]; rfl
    _ ≤ _ := key
    _ ≤ ENNReal.ofReal (K' * Real.exp (-c * a)) * (L * ENNReal.ofReal S0) +
        L * ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) +
        ENNReal.ofReal (K' ^ 2 / 2) * (L * ENNReal.ofReal (μT * Ct * bracketBias d s N)) := by
      gcongr
    _ = L * (ENNReal.ofReal (K' * Real.exp (-c * a) * S0) +
        ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) +
        ENNReal.ofReal (K' ^ 2 / 2 * (μT * Ct * bracketBias d s N))) := by
      rw [rbs_ofReal_comm (by positivity), rbs_ofReal_comm (by positivity)]
      ring
    _ = L * ENNReal.ofReal (K' * Real.exp (-c * a) * S0 + Real.sqrt Crem * Real.sqrt (deltaN d s N) +
        K' ^ 2 / 2 * (μT * Ct * bracketBias d s N)) := by
      have e1 : 0 ≤ K' * Real.exp (-c * a) * S0 := by positivity
      have e2 : 0 ≤ Real.sqrt Crem * Real.sqrt (deltaN d s N) := by positivity
      have e3 : 0 ≤ K' ^ 2 / 2 * (μT * Ct * bracketBias d s N) := by positivity
      rw [ENNReal.ofReal_add (add_nonneg e1 e2) e3, ENNReal.ofReal_add e1 e2]
    _ ≤ L * ENNReal.ofReal (C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N))) := by
      gcongr
      have h3 : K' ^ 2 / 2 * (μT * Ct * bracketBias d s N) ≤ K' ^ 2 * (μT * Ct) * Real.sqrt (deltaN d s N) := by
        have : 0 ≤ K' ^ 2 / 2 * (μT * Ct) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hbb this]
      have h4 : Real.sqrt Crem * Real.sqrt (deltaN d s N) +
          K' ^ 2 * (μT * Ct) * Real.sqrt (deltaN d s N) ≤ C * Real.sqrt (deltaN d s N) := by
        nlinarith [mul_le_mul_of_nonneg_right hC2 hsq0]
      nlinarith [mul_le_mul_of_nonneg_right hC1 hexp0]
    _ = ENNReal.ofReal C * L * ENNReal.ofReal (Real.exp (-c * a) + Real.sqrt (deltaN d s N)) := by
      rw [ENNReal.ofReal_mul hC0.le]
      ring

end HRS.ME.Ret

end
