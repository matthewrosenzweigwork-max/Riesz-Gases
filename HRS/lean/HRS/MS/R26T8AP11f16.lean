import HRS.MS.R26T8AP11f15
import HRS.MS.R26T8AP11kc

/-!
# S8.2 T8A P11f (part 16): global jet bound for the smooth kernel `Kc` (radius `δ = 1/2`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_f16_Kc_global (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (k : ℕ) :
    ∃ BK : ℝ, 0 ≤ BK ∧ ∀ i ≤ k, ∀ u : Euc d,
      ‖iteratedFDeriv ℝ i (r26t8a_Kc alpha chi (1 / 2 : ℝ)) u‖ ≤ BK := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨C, hC0, hC⟩ := r26t8a_Kc_jets d hd alpha halpha had chi hchi hδ k
  have hKs := r26t8a_Kc_contDiff d hd alpha halpha had chi hchi hδ
  have hloc : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u : Euc d, ‖u‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ i (r26t8a_Kc alpha chi (1 / 2 : ℝ)) u‖ ≤ B := by
    intro i
    have hcont : Continuous (iteratedFDeriv ℝ i (r26t8a_Kc alpha chi (1 / 2 : ℝ))) :=
      hKs.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euc d) (1 / 2)).exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun u hu => (hB u (by simpa using hu)).trans (le_max_left _ _)⟩
  choose B hB0 hB using hloc
  refine ⟨C + ∑ i ∈ Finset.range (k + 1), B i, add_nonneg hC0 (Finset.sum_nonneg fun i _ => hB0 i), ?_⟩
  intro i hi u
  have hsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), B i := Finset.sum_nonneg fun i _ => hB0 i
  by_cases hu : (1 / 2 : ℝ) ≤ ‖u‖
  · have := hC i hi u hu
    linarith
  · have h1 := hB i u (not_le.1 hu).le
    have h2 : B i ≤ ∑ i ∈ Finset.range (k + 1), B i :=
      Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_range.2 (by omega))
    linarith

end HRS.MS.R26T8A
