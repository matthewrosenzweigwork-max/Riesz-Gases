import HRS.ME.RetBurnStmt
import HRS.ME.RetBurnInitA
import HRS.ME.RetBurnInitB

/-!
# Row 5.10: `RetBurnInit` (the window starting at time `0`, the initial field retained)

The weight `w = h ∘ X 0` is `ℱ 0`-measurable and bounded; the weighted engine `ret_engine_core_proof` is applied with `a = 0` and
`X₀' = zetaE (X 0)`, so that the initial term vanishes.  The comparison law is the window of a linear fluctuation solution whose
initial law is the weighted law of `ζ^0`.  The remainder majorant and the trace majorant are bounded in `L²` and the weight is
separated by Cauchy-Schwarz.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn HRS.MD.EQTrace

/-- Square-root form of a second-moment bound. -/
theorem ret_b3_l2_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞) {A : ℝ}
    (hA : 0 ≤ A) (h : ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal A) :
    (∫⁻ ω, f ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt A) := by
  calc (∫⁻ ω, f ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal A) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt A) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← Real.sqrt_eq_rpow]

set_option maxHeartbeats 1600000 in
theorem ret_burn_init_proof (d : ℕ) : RetBurnInit d := by
  classical
  intro hd s hs0 hsd V hV β hβ ρβ hρβ m hm T hT
  have hm0 : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmd2' : (d : ℝ) + 2 < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm0
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm0
  have hmd2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  obtain ⟨K, c, Cmax, hK, hc, hCmax, hevo⟩ :=
    HRS.MD.EQBurnWire.eqbw_evoPkg (d := d) hd hs0 hsd V hV β β hβ le_rfl m T hT.le
  obtain ⟨Vev, hEv, hdual⟩ := hevo β hβI ρβ hρβ
  have hEv' := eqb_ev_max hEv
  set K' : ℝ := max K 1 with hK'def
  have hK'0 : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K' * Real.exp (-c * (t - u)) := hEv'.decay
  obtain ⟨Crem, hCrem0, hrem⟩ := HRS.MD.EQRem.eq_rem_integrated_proof hd hs0 hsd V hV β β hβ le_rfl m hmd T
    hT.le K' c hK'0.le hc
  obtain ⟨Ct, hCt0, htr⟩ := ret_b3_trace_L2 hd hs0 hsd V hV hβ m hm1 (S := 0 + T) (by linarith)
  set C : ℝ := Real.sqrt Crem + K' ^ 2 * Ct + 1 with hCdef
  have hC0 : 0 < C := by positivity
  refine ⟨C, hC0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hX h hhm hbd h1
  obtain ⟨Mb, hMb⟩ := hbd
  have hX' : IsStationaryGibbsFlow P s hs0 hsd V β hβ (0 + T) X₀ W X := by rwa [zero_add]
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  have hXm : ∀ t, Measurable (X t) := fun t => (hF.adapted t).mono (ℱ.le t) le_rfl
  have hX0ae : ∀ᵐ ω ∂P, X 0 ω = X₀ ω := by
    rcases hX.flow.flow with ⟨hsol, -⟩ | ⟨hd1, -⟩
    · exact hsol.init
    · omega
  have hX₀m : Measurable X₀ := hX.flow.init_meas
  set w : Ω → ℝ≥0∞ := fun ω => h (X 0 ω) with hw
  have hwm' : Measurable[ℱ 0] w := hhm.comp (hF.adapted 0)
  have hwm : Measurable w := hwm'.mono (ℱ.le 0) le_rfl
  have hB : ∀ ω, w ω ≤ Mb := fun ω => hMb _
  have hwae : (fun ω => h (X₀ ω)) =ᵐ[P] w := hX0ae.mono fun ω hω => by simp [hw, hω]
  have h1' : ∫⁻ ω, w ω ∂P = 1 := by rw [← h1]; exact (lintegral_congr_ae hwae).symm
  have hwd : P.withDensity (fun ω => h (X₀ ω)) = P.withDensity w := withDensity_congr_ae hwae
  have hA : (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) = ∫⁻ ω, w ω ^ 2 ∂P :=
    lintegral_congr_ae (hwae.mono fun ω hω => congrArg (· ^ 2) hω)
  haveI hPw : IsProbabilityMeasure (P.withDensity w) :=
    isProbabilityMeasure_withDensity_of_lintegral_eq_one P hwm h1'
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  set X₀' : Ω → NegSobolev d m := fun ω => zetaE m (P.map (X 0)) (X 0 ω) with hX₀'def
  have hX₀'ℱ : Measurable[ℱ 0] X₀' :=
    (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable.comp (hF.adapted 0)
  have hX₀'m : Measurable X₀' := hX₀'ℱ.mono (ℱ.le 0) le_rfl
  haveI : IsProbabilityMeasure ((P.withDensity w).map X₀') :=
    (Measure.isProbabilityMeasure_map_iff hX₀'m.aemeasurable).2 inferInstance
  obtain ⟨Ω', mΩ', P', hP', Y₀, Y, hY₀m, hY₀law, hsol⟩ :=
    ret_b3_linear_exists hd hs0 hsd V hV hβ ρβ hρβ m hmd2' hT ((P.withDensity w).map X₀')
  have htr' := eqb_traj hd hs0 hsd V hV hβ ρβ hρβ
  have hY : IsLinearFluctuationSolution P' htr'.dyn (fun _ => ρβ) m β⁻¹ (0 + T) Y₀ Y := by
    rw [zero_add]; exact hsol
  have hid0 := t25p_hid hd htr' hmd hT (le_refl (0 : ℝ)) hK'0 hc hdual hEv' P' Y₀ hY₀m Y hY
    ((P.withDensity w).map X₀') hY₀law (law P' (Main.windowPath m T 0 Y)) rfl
  have key := ret_engine_core_proof hd hs0 hsd V hV hβ ρβ hρβ m hm0 hK'0 hc hT Vev hEv' hdual
    (le_refl (0 : ℝ)) hN P X₀ W X hX' ℱ W' hF X₀' hX₀'ℱ w hwm' hB h1' (law P' (Main.windowPath m T 0 Y)) hid0
  -- the three bounds
  obtain ⟨-, hB1, hB2⟩ := hrem β hβI ρβ hρβ 0 le_rfl N hN P X₀ W X hX' Vev hdual hdec
  have hBmeas := ret_b3_remMeas hd hs0 hsd V hV hβ ρβ hρβ m hm0 hT Vev hEv' hdual (le_refl (0 : ℝ)) hN
    P X₀ W X hX' ℱ W' hF
  obtain ⟨hFmeas, hFmaj, hF2⟩ := htr ρβ hρβ N hN P X₀ W X hX' ℱ W' hF
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
  have hb0 : 0 ≤ bracketBias d s N := HRS.MD.EQTrace.eqtrace_b_nonneg (d := d) hs0 (by omega)
  have hbb : bracketBias d s N ≤ 2 * Real.sqrt (deltaN d s N) :=
    bracketBias_le_sqrt_deltaN (by omega) hs0 hsd (by omega)
  set A : ℝ≥0∞ := (∫⁻ ω, w ω ^ 2 ∂P) ^ (1 / 2 : ℝ) with hAdef
  -- the initial term vanishes
  have hT1 : ∫⁻ ω, w ω * ‖zetaE m (P.map (X 0)) (X 0 ω) - X₀' ω‖ₑ ∂P = 0 := by
    simp [hX₀'def]
  -- the remainder term
  have hT2 : ∫⁻ ω, w ω * (⨆ t ∈ ratTimes 0 T,
        (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ X k t ω)) ^ (1 / 2 : ℝ)) ∂P ≤
      A * ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) := by
    refine (lintegral_mul_le_L2 P hwm.aemeasurable hBmeas).trans (mul_le_mul' le_rfl ?_)
    have := ret_b3_l2_le P _ (mul_nonneg hCrem0.le hδ0) hB2
    rwa [Real.sqrt_mul hCrem0.le] at this
  -- the trace term
  have hJle : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) (0 + T),
      ENNReal.ofReal (Real.exp (-c * max (0 - r) 0) ^ 2 *
        traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
          covForm m β⁻¹ (withDensityReal ρβ)))) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) (0 + T), traceMaj m β⁻¹ ρβ (X (min (0 + T) r).toNNReal ω) := by
    intro ω
    refine le_trans (lintegral_mono fun r => ?_) (hFmaj ω)
    have he : Real.exp (-c * max (0 - r) 0) ^ 2 ≤ 1 := by
      refine pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.2 ?_)
      have : 0 ≤ max (0 - r) 0 := le_max_right _ _
      nlinarith
    rw [ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (Real.exp (-c * max (0 - r) 0) ^ 2) *
          ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ)))
        ≤ 1 * ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ))) := by
          gcongr
          exact ENNReal.ofReal_le_one.2 he
      _ = _ := one_mul _
  have hT3 : ∫⁻ ω, w ω * (∫⁻ r in Set.Icc (0 : ℝ) (0 + T),
        ENNReal.ofReal (Real.exp (-c * max (0 - r) 0) ^ 2 *
          traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
            covForm m β⁻¹ (withDensityReal ρβ)))) ∂P ≤
      A * ENNReal.ofReal (Ct * bracketBias d s N) := by
    calc _ ≤ ∫⁻ ω, w ω * (∫⁻ r in Set.Icc (0 : ℝ) (0 + T),
            traceMaj m β⁻¹ ρβ (X (min (0 + T) r).toNNReal ω)) ∂P :=
          lintegral_mono fun ω => mul_le_mul' le_rfl (hJle ω)
      _ ≤ A * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (0 + T),
            traceMaj m β⁻¹ ρβ (X (min (0 + T) r).toNNReal ω)) ^ 2 ∂P) ^ (1 / 2 : ℝ) :=
          lintegral_mul_le_L2 P hwm.aemeasurable hFmeas.aemeasurable
      _ ≤ A * ENNReal.ofReal (Real.sqrt ((Ct * bracketBias d s N) ^ 2)) :=
          mul_le_mul' le_rfl (ret_b3_l2_le P _ (sq_nonneg _) hF2)
      _ = A * ENNReal.ofReal (Ct * bracketBias d s N) := by
          rw [Real.sqrt_sq (mul_nonneg hCt0.le hb0)]
  -- the law of the window
  have hfun : (Uniform.windowPath (0 : ℝ) T (fun t ω' => zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω')) :
      Ω → PathSp T (NegSobolev d m)) = Main.windowZeta m T 0 P X :=
    funext (eqb_windowPath_eq P m T 0 X)
  have key' : ENNReal.ofReal (smoothDist 2 ((P.withDensity w).map (Main.windowZeta m T 0 P X))
        (law P' (Main.windowPath m T 0 Y))) ≤
      ENNReal.ofReal (K' * Real.exp (-c * 0)) *
          ∫⁻ ω, w ω * ‖zetaE m (P.map (X 0)) (X 0 ω) - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, w ω * (⨆ t ∈ ratTimes 0 T,
          (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ X k t ω)) ^ (1 / 2 : ℝ)) ∂P +
        ENNReal.ofReal (K' ^ 2 / 2) *
          ∫⁻ ω, w ω * (∫⁻ r in Set.Icc (0 : ℝ) (0 + T),
            ENNReal.ofReal (Real.exp (-c * max (0 - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
                covForm m β⁻¹ (withDensityReal ρβ)))) ∂P := by
    rw [← hfun]; exact key
  refine ⟨Ω', mΩ', P', hP', Y₀, Y, hsol, ?_, ?_⟩
  · rw [hwd]; exact hY₀law
  · rw [hwd, hA]
    refine key'.trans ?_
    rw [hT1, mul_zero, zero_add]
    have hbd2 : ENNReal.ofReal (Ct * bracketBias d s N) ≤ ENNReal.ofReal (Ct * (2 * Real.sqrt (deltaN d s N))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbb hCt0.le)
    have hsq := Real.sqrt_nonneg (deltaN d s N)
    calc _ ≤ A * ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) +
          ENNReal.ofReal (K' ^ 2 / 2) * (A * ENNReal.ofReal (Ct * (2 * Real.sqrt (deltaN d s N)))) :=
          add_le_add hT2 (mul_le_mul' le_rfl (hT3.trans (mul_le_mul' le_rfl hbd2)))
      _ = A * (ENNReal.ofReal (Real.sqrt Crem * Real.sqrt (deltaN d s N)) +
          ENNReal.ofReal (K' ^ 2 / 2) * ENNReal.ofReal (Ct * (2 * Real.sqrt (deltaN d s N)))) := by ring
      _ = A * ENNReal.ofReal ((Real.sqrt Crem + K' ^ 2 * Ct) * Real.sqrt (deltaN d s N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
      _ ≤ A * ENNReal.ofReal (C * Real.sqrt (deltaN d s N)) := by
          gcongr
          nlinarith
      _ = ENNReal.ofReal C * A * ENNReal.ofReal (Real.sqrt (deltaN d s N)) := by
          rw [ENNReal.ofReal_mul hC0.le]; ring

end HRS.ME.Ret

end
