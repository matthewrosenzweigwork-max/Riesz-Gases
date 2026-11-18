import HRS.ME.CritSpec
import HRS.MD.EQAsmDirect
import HRS.MD.EQLawFlow
import HRS.MD.EQLawPath
import HRS.MD.EQBurnWire
import HRS.MD.EQInterpWin
import HRS.MD.EQGaussWindow
import HRS.Prob.Metrics

/-!
# Chunk E, row 2.10 path clauses: assembly of `critical_centered_path` (A5)

`crit_paths_of_burnin`: the frozen `HRS.Main.critical_centered_path` from the critical burn-in
`HRS.ME.Crit.crit_burnin_of_evo` (as a hypothesis) and the forcing bound `CritForcing` for all data.

Route (as `HRS.MD.EQAsmDirect.eq_direct_assembly_proof`): the evolution package of `eqbw_evoPkg` at
`s = d/2`; the burn-in at the rational window starts `a = n ∈ ℕ`, with the flow on `n + T` supplied by
`eq_flow_exists_proof` and the window law identified by `eq_path_stationary_proof`; the limit `n → ∞`
gives the `W_2` bound with `C N^{-1/2}`.  Then `W_p` for `1 ≤ p ≤ 2` by `wassersteinE_mono`, and
`d_k ≤ d_1 ≤ W_1 ≤ W_2` by `smoothDist_succ_le`, `smoothDist_one_le_wasserstein`, `wassersteinE_one_le_two`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritPaths

open HRS HRS.LZ HRS.Uniform HRS.Main

theorem crit_paths_of_burnin {d : ℕ}
    (hburn : type_of% (@HRS.ME.Crit.crit_burnin_of_evo d))
    (hforce : ∀ (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
      (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T),
      HRS.ME.Crit.CritForcing d hs0 hsd V βm βp hβm m T) :
    type_of% (@HRS.Main.critical_centered_path d) := by
  intro hd hs0 hsd V hV βm βp hβm hββ m hm T hT
  obtain ⟨K, c0, Cmax, hK, hc0, hCmax, hevo⟩ :=
    HRS.MD.EQBurnWire.eqbw_evoPkg (d := d) (s := (d : ℝ) / 2) hd hs0 hsd V hV βm βp hβm hββ m T hT.le
  obtain ⟨C, c, hC, hc, h⟩ :=
    hburn hd hs0 hsd V hV βm βp hβm hββ m hm T hT K c0 Cmax hK hc0 hCmax hevo
      (hforce hd hs0 hsd V hV βm βp hβm hββ m hm T hT)
  refine ⟨C, hC, ?_⟩
  intro β hβ ρβ hρ u hu N hN Ω _ P _ X₀ W X hSel hfilt hlawX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hmd : (d : ℝ) / 2 < m := by linarith
  have hdm : (d : ℝ) < 2 * m := by linarith
  have hfl : HRS.LZ.IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β hβ0 (u + T) X₀ W X :=
    ⟨hSel, hfilt, hlawX⟩
  -- the burn-in at the integer window starts `a = n`, transported to the window at `u`
  have key : ∀ n : ℕ, wassersteinE 2 (law P (HRS.Main.windowZeta m T u P X))
      (law P' (HRS.Main.windowPath m T 0 Z)) ≤
      ENNReal.ofReal (C * (Real.exp (-c * (n : ℝ)) + (N : ℝ) ^ (-(1 : ℝ) / 2))) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    obtain ⟨Ω'', _, P'', _, X₀', W', X', hX'⟩ :=
      HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ0 hN ((n : ℝ) + T) (by linarith)
    rw [HRS.MD.EQLawPath.eq_path_stationary_proof hd hs0 hsd V hV hβ0 m hmd T hT0 hN P X₀ W X u hu
      hfl P'' X₀' W' X' (n : ℝ) hn0 hX']
    exact h β hβ ρβ hρ (n : ℝ) hn0 ⟨(n : ℚ), by simp⟩ N hN P'' X₀' W' X' hX' P' Z hZ
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW2 : wassersteinE 2 (law P (HRS.Main.windowZeta m T u P X))
      (law P' (HRS.Main.windowPath m T 0 Z)) ≤
      ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => -c * (n : ℝ)) atTop atBot :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp h2
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (Real.exp (-c * (n : ℝ)) +
        (N : ℝ) ^ (-(1 : ℝ) / 2)))) atTop
        (𝓝 (ENNReal.ofReal (C * (0 + (N : ℝ) ^ (-(1 : ℝ) / 2))))) :=
      ENNReal.tendsto_ofReal ((hexp.add_const ((N : ℝ) ^ (-(1 : ℝ) / 2))).const_mul C)
    have := ge_of_tendsto hlim (Eventually.of_forall key)
    simpa only [zero_add] using this
  -- probability laws of the two windows
  haveI : IsProbabilityMeasure (law P (HRS.Main.windowZeta m T u P X)) :=
    (Measure.isProbabilityMeasure_map_iff
      (HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ0 hN hu hT0 P hfl hdm)).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (HRS.Main.windowPath m T 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff
      (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m T P' Z hZ 0 le_rfl).1).2 inferInstance
  have hC0 : 0 ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2) := mul_nonneg hC.le hNpow
  refine ⟨hW2, ?_, ?_⟩
  · intro p hp1 hp2
    exact (HRS.wassersteinE_mono p 2 hp1 hp2 _ _).trans hW2
  · intro k hk
    have hsucc : ∀ j : ℕ,
        smoothDist (j + 1) (law P (HRS.Main.windowZeta m T u P X))
          (law P' (HRS.Main.windowPath m T 0 Z)) ≤
        smoothDist 1 (law P (HRS.Main.windowZeta m T u P X))
          (law P' (HRS.Main.windowPath m T 0 Z)) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact (HRS.smoothDist_succ_le (j + 1) _ _).trans ih
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : ENNReal.ofReal (smoothDist 1 (law P (HRS.Main.windowZeta m T u P X))
        (law P' (HRS.Main.windowPath m T 0 Z))) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) :=
      (HRS.smoothDist_one_le_wasserstein _ _).trans
        ((HRS.wassersteinE_one_le_two _ _).trans hW2)
    exact (hsucc j).trans ((ENNReal.ofReal_le_ofReal_iff hC0).1 h1)

end HRS.ME.CritPaths

end
