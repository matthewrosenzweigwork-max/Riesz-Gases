import HRS.MS.R26T8AP11f18
import HRS.MS.S82P2Local

/-!
# S8.2 T8A P11f (part 19): bounded jets of cutoff-type functions, and the three cutoffs
`r26t8a_f19_bdd_jets`: a `C^∞` function that is constant outside a ball has bounded jets of every finite order.
`ψ0 v = chi (4v)`, `θ1 = 1 - ψ0`, `θ2 = θ1 * chi`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f19_bdd_jets {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {c R : ℝ}
    (hc : ∀ v : Euc d, R ≤ ‖v‖ → F v = c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j F v‖ ≤ C := by
  have hloc : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Euc d, ‖v‖ ≤ R → ‖iteratedFDeriv ℝ j F v‖ ≤ B := by
    intro j
    have hcont : Continuous (iteratedFDeriv ℝ j F) :=
      hF.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euc d) R).exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun v hv => (hB v (by simpa using hv)).trans (le_max_left _ _)⟩
  choose B hB0 hB using hloc
  refine ⟨∑ j ∈ Finset.range (k + 1), B j + |c|, add_nonneg (Finset.sum_nonneg fun j _ => hB0 j) (abs_nonneg _), ?_⟩
  intro j hj v
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1), B j := Finset.sum_nonneg fun j _ => hB0 j
  have h2 : B j ≤ ∑ j ∈ Finset.range (k + 1), B j :=
    Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_range.2 (by omega))
  by_cases hv : ‖v‖ ≤ R
  · have := hB j v hv
    linarith [abs_nonneg c]
  · have hv' : R < ‖v‖ := not_le.1 hv
    have hopen : IsOpen {w : Euc d | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : F =ᶠ[𝓝 v] fun _ => c := by
      filter_upwards [hopen.mem_nhds hv'] with w hw
      exact hc w (le_of_lt hw)
    rw [(hev.iteratedFDeriv ℝ j).self_of_nhds]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      linarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
    · have h0 : iteratedFDeriv ℝ j (fun _ : Euc d => c) v = 0 := by
        simp [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
      rw [h0, norm_zero]
      linarith [abs_nonneg c]

end HRS.MS.R26T8A
