import HRS.MS.SA12X3P2C
import HRS.MS.SA12K20

/-!
# S.A.12 P2 (SA12X3), part D: the limit weak operator of a `C_c^∞` test function has a finite `ℓ¹(L²)` norm
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12x3p_op_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∃ K : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (weakOp (D.coeff μ) t σ ψ) ≤ ENNReal.ofReal K := by
  obtain ⟨R0, hR0⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨R1, A, hR1, hA0, hjet, -⟩ := sa12k_psi_data hψ
  set R : ℝ := max R0 1 with hR
  have hRR : 1 ≤ R := le_max_right _ _
  have hts : tsupport ψ ⊆ closedBall (0 : Euc d) R :=
    hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨K0, hK0, hK⟩ := sa12y_weakOp_bound hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD R hRR
  obtain ⟨CA, hCA, hcell⟩ := sa12y_cell_decay hd
  refine ⟨CA * (K0 * A), fun σ hσ => hcell _ (K0 * A) (by positivity) fun x => ?_⟩
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have := hK ψ A hψ.1 hts hA0 hjet (t - σ) hr x
  exact this

end HRS.MH.AdjointRd.Phase2SA12Assembly
