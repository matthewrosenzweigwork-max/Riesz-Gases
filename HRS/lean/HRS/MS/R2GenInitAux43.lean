import HRS.MS.R2GenInitAux41
import HRS.MS.R2GenInitStat

/-!
# S10.5 for the stationary trajectory, unconditional: the window comparison `S105CompareStat`

`s105_compare_stat`: `S105CompareStat d s a β T` for `d ≥ 2`, `0 ≤ s < d`, `a, β, T > 0`, proved from the master window comparison `s105_master`
(smooth and `W_1` bounds with constants independent of `b`, `N`, the realization and the prescribed field) and the abstract window comparison
`s105_win_compare`.  Consequently `r2_window_general_initial_stationary` is unconditional.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

open HRS HRS.MS.R2GenInit HRS.MS.GenPath HRS.Whole.AppendixA

variable {d : ℕ}

theorem s105_compare_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) : S105CompareStat d s a β T := by
  obtain ⟨Cs, Cw, hCs, hCw, hCmp⟩ := s105_win_compare (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T hT
  refine ⟨max 1 (max Cs Cw), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro ρ hρ N hN _ Ω _ P _ X₀ W X hreal _ η₀ _ Y hY hcontc b hb F Wt hFb hBt
  have hd1 : 1 ≤ d := by omega
  have hT0 : 0 ≤ T := hT.le
  have hτ' : 0 < b + T := by linarith
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hS : S105Stat d s a β T b ρ := s105_stat_of_thermal hd hs0 hsd ha hβ hT hρ hb
  obtain ⟨hsm, hw1⟩ := s105_master hCmp hd hs0 hsd ha hβ hT hρ hb hN P X₀ W X hreal η₀ Y hY (hcontc b hb) F Wt hFb hBt
  haveI hνp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hS.hprob
  have hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X := hreal.solution (b + T)
  have hΞP : AEMeasurable (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ)) P := by
    have e : flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) X (fun _ : ℝ => ρ) =
        HRS.Uniform.windowPath b T (s105Xi ((wholeSpaceIndex d : ℕ) : ℝ) (Real.sqrt N) ρ X) := by
      funext ζ
      unfold flucPathW windowPathOf HRS.Uniform.windowPath s105Xi
      rfl
    rw [e]
    refine HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hτ' _ (fun t _ => ?_) ?_
    · unfold s105Xi
      exact (haveI := hνp; s56_xi_cont_config hd1 hm (Real.sqrt N) (by omega : 0 < N) (HRS.Whole.withDensityReal ρ)).measurable.comp
        (hX.adapted _)
    · filter_upwards [hX.cont] with ζ hζ
      exact s56_xi_cont_time hd1 hm (Real.sqrt N) (by omega : 0 < N) (T := b + T) (fun _ => ρ) (fun t _ => hS.hprob)
        (fun ψ _ _ => continuousOn_const) (fun t => X (Real.toNNReal t) ζ)
        (fun i => (hζ i).comp continuous_real_toNNReal)
  have hYP : AEMeasurable (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y) P := by
    have e : processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T b Y = HRS.Uniform.windowPath b T Y := by
      funext ζ
      unfold processWindow windowPathOf HRS.Uniform.windowPath
      rfl
    rw [e]
    exact HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hτ' _ (fun t _ => (hY (b + T)).meas t)
      (hY (b + T)).cont
  refine ⟨hΞP, hYP, ?_, ?_⟩
  · refine hsm.trans ?_
    have h1 : ENNReal.ofReal Cs ≤ ENNReal.ofReal (max 1 (max Cs Cw)) :=
      ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (max Cs Cw)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc ENNReal.ofReal Cs * Wt + F + _
        ≤ ENNReal.ofReal (max 1 (max Cs Cw)) * Wt + ENNReal.ofReal (max 1 (max Cs Cw)) * F +
          ENNReal.ofReal (max 1 (max Cs Cw)) * _ := by
          gcongr
          · exact le_mul_of_one_le_left bot_le h2
          · exact le_mul_of_one_le_left bot_le h2
      _ = _ := by ring
  · refine hw1.trans ?_
    have h1 : ENNReal.ofReal Cw ≤ ENNReal.ofReal (max 1 (max Cs Cw)) :=
      ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (max Cs Cw)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + _
        ≤ ENNReal.ofReal (max 1 (max Cs Cw)) * Wt ^ (1 / 2 : ℝ) + ENNReal.ofReal (max 1 (max Cs Cw)) * F +
          ENNReal.ofReal (max 1 (max Cs Cw)) * _ := by
          gcongr
          · exact le_mul_of_one_le_left bot_le h2
          · exact le_mul_of_one_le_left bot_le h2
      _ = _ := by ring

end HRS.Whole
