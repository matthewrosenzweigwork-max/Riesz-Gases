import HRS.MD.EQBurnBurnEngine
import HRS.MD.EQBurnBurnTrace
import HRS.MD.EQBurnBurnInit
import HRS.MD.EQBurnBurnArith
import HRS.MD.EQBurnDefs

/-!
# Packet EQ-BURN P4 (chunk D): `eq_burnin_of_evo_proof`

Relocated proof of `HRS.MD.EQBurn.eq_burnin_of_evo` (frozen with its `sorry` in `HRS/MD/EQBurnSpec.lean`; the tie `HRS/MD/EQBurnBurnTie.lean`
checks that the statements agree).  Route: `eqb_engine` (enlargement by P3, particle martingale, convolution, mild identity, remainder majorant,
`t25p_hid` with P2, `t25p_stage2`), then the three terms are bounded by EQ-INITMOM, EQ-REM and EQ-TRACE (`eqb_trace_int`) and the
arithmetic of `EQ29Vocab` (`b_N ≤ 2√δ_N`, `√b_N ≤ N^{-1/4} + √δ_N`) gives the two inequalities of `BurninConcl`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurn

variable {d : ℕ}

theorem eqb_ev_max {m K c T Cmax : ℝ} {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (h : T25Ev m K c T Cmax Vev) : T25Ev m (max K 1) c T Cmax Vev :=
  ⟨h.plain, fun u t hu hut => (h.decay u t hu hut).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le), h.maxM, h.exists_conv⟩

theorem eq_burnin_of_evo_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 < T)
    (K c Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hCmax : 0 ≤ Cmax)
    (hevo : EvoPkg d s hs0 hsd V βm βp hβm m K c T Cmax) :
    BurninConcl d s hs0 hsd V βm βp hβm m T := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hm1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmh : (d : ℝ) / 2 < m := by linarith
  set K' : ℝ := max K 1 with hK'def
  have hK'0 : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Crem, hCrem0, hrem⟩ := HRS.MD.EQRem.eq_rem_integrated_proof hd hs0 hsd V hV βm βp hβm hββ m hmd T
    hT.le K' c hK'0.le hc
  obtain ⟨Ct, hCt0, htr⟩ := eqb_trace_int hd hs0 hsd V hV βm βp hβm hββ m hm1 hc hT.le
  obtain ⟨Cp, hCp0, hinp⟩ := HRS.MD.EQInit.eq_init_particle_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  obtain ⟨Cg, hCg0, hing⟩ := HRS.MD.EQInit.eq_init_gauss_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  set S0 : ℝ := Real.sqrt Cp + Real.sqrt Cg with hS0def
  have hS00 : 0 ≤ S0 := by positivity
  set Q : ℝ := 2 * (K' ^ 2 + Real.sqrt Cmax) + K' + 1 with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set C : ℝ := max (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct)) + 1
    with hCdef
  have hC1 : K' * S0 ≤ C := by
    have := le_max_left (K' * S0) (Crem + K' ^ 2 * Ct)
    have := le_max_left (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct))
    linarith
  have hC2 : Crem + K' ^ 2 * Ct ≤ C := by
    have := le_max_right (K' * S0) (Crem + K' ^ 2 * Ct)
    have := le_max_left (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct))
    linarith
  have hC3 : Q * S0 ≤ C := by
    have := le_max_left (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct)
    have := le_max_right (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct))
    linarith
  have hC4 : Real.sqrt Crem + Q * Real.sqrt Ct ≤ C := by
    have := le_max_right (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct)
    have := le_max_right (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct))
    linarith
  have hC0 : 0 < C := by
    have : 0 ≤ K' * S0 := by positivity
    have := le_max_left (K' * S0) (Crem + K' ^ 2 * Ct)
    have := le_max_left (max (K' * S0) (Crem + K' ^ 2 * Ct)) (max (Q * S0) (Real.sqrt Crem + Q * Real.sqrt Ct))
    linarith
  refine ⟨C, c, hC0, hc, ?_⟩
  intro β hβ ρβ hρβ a ha N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  obtain ⟨Vev, hEv, hdual⟩ := hevo β hβ ρβ hρβ
  have hEv' := eqb_ev_max hEv
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K' * Real.exp (-c * (t - u)) := hEv'.decay
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hη'm, hη'map, E1, E2⟩ :=
    eqb_engine hd hs0 hsd V hV hβ0 ρβ hρβ m hm hK'0 hc hT Vev hEv' hdual ha hN P X₀ W X hX P' Z hZ
  -- stationarity on the enlarged space
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 (a + T) hN P₁ _ _ _ hX'
  have hYm : ∀ t : ℝ≥0, Measurable (fun ω' => X t (π ω')) := fun t =>
    (hF'.adapted t).mono (ℱ₁.le t) le_rfl
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hmd2 : (d : ℝ) < 2 * m := by linarith
  -- the initial term
  have hzm : Measurable (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) :=
    (EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable
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
    exact hinp β hβ ρβ hρβ N hN
  have hI2 : ∫⁻ ω, ‖η' ω‖ₑ ^ 2 ∂P₁ ≤ ENNReal.ofReal Cg := by
    have h1 := lintegral_map (μ := P₁) (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := η')
      (measurable_enorm.pow_const 2) hη'm
    have h2 := lintegral_map (μ := P') (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := Z 0)
      (measurable_enorm.pow_const 2) (hZ.meas 0)
    rw [← h1, hη'map, h2]
    exact hing β hβ ρβ hρβ P' Z hZ
  obtain ⟨hD1, hD2⟩ := eqb_init_diff P₁ _ η' hζ0m.aemeasurable hη'm.aemeasurable hCp0.le hCg0.le hI1 hI2
  -- the remainder term
  obtain ⟨-, hB1, hB2⟩ := hrem β hβ ρβ hρβ a ha N hN P₁ _ _ _ hX' Vev hdual hdec
  -- the trace term
  have hJ := htr β hβ ρβ hρβ a ha N hN P₁ _ _ _ hX' ℱ₁ W'' hF'
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
  have hb0 : 0 ≤ bracketBias d s N := HRS.MD.EQTrace.eqtrace_b_nonneg (d := d) hs0 (by omega)
  have hbb : bracketBias d s N ≤ 2 * Real.sqrt (deltaN d s N) :=
    bracketBias_le_sqrt_deltaN (by omega) hs0 hsd (by omega)
  have hsb : Real.sqrt (bracketBias d s N) ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N) :=
    sqrt_bracketBias_le (by omega) hδ0
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hexp0 : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · exact eqb_smooth_arith hK'0.le hexp0 hS00 hCrem0.le hCt0.le hδ0 hb0 hD1 hB1 hJ hbb hC1 hC2 E1
  · have hE := E2 2 (Or.inr rfl)
    refine eqb_wass_arith hQ0 hexp0 hS00 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hn0 hδ0 hD2 ?_ ?_ hC3 hC4 hE
    · have h2 := eqb_l2_le P₁ (fun ω => ⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ
          (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) (mul_nonneg hCrem0.le hδ0) hB2
      rw [Real.sqrt_mul hCrem0.le] at h2
      exact h2
    · have h3 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
              traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal (π ω))) -
                covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (Real.sqrt Ct * Real.sqrt (bracketBias d s N)) := by
        calc _ ≤ (ENNReal.ofReal (Ct * bracketBias d s N)) ^ (1 / 2 : ℝ) :=
              ENNReal.rpow_le_rpow hJ (by norm_num)
          _ = ENNReal.ofReal (Real.sqrt Ct * Real.sqrt (bracketBias d s N)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCt0.le hb0) (by norm_num), ← Real.sqrt_eq_rpow,
                Real.sqrt_mul hCt0.le]
      refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left hsb (Real.sqrt_nonneg _)

end HRS.MD.EQBurnBurn

end
