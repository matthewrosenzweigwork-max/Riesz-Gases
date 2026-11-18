import HRS.MS.SA12K17

/-!
# S.A.12 L8: the limit weak operator decays like `⟨x⟩^{-(d+3)}`, uniformly in `σ ∈ [0,t]`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12k_hldec (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ σ ∈ Icc (0 : ℝ) t, ∀ x,
      |weakOp (D.coeff μ) t σ ψ x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨R0, hR0⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hsupp : tsupport ψ ⊆ Metric.closedBall (0 : Euc d) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨K, hK0, hK⟩ := sa12y_weakOp_bound hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD R hR1
  have hb : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ B := by
    intro i
    have hc : Continuous (iteratedFDeriv ℝ i ψ) :=
      hψ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hψ.2.iteratedFDeriv i)
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hb
  set A : ℝ := B 0 + B 1 + B 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith [hB0 0, hB0 1, hB0 2]
  refine ⟨K * A, by positivity, fun σ hσ x => ?_⟩
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have h := hK ψ A hψ.1 hsupp hA0 (fun i hi x => by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · linarith [hB 0 x, hB0 1, hB0 2]
    · linarith [hB 1 x, hB0 0, hB0 2]
    · linarith [hB 2 x, hB0 0, hB0 1]) (t - σ) hr x
  exact h

end HRS.MH.AdjointRd.Phase2SA12Limit
