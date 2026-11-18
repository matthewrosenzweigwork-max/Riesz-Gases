import HRS.MS.SA12Z3NearN7H

/-!
# S.A.12 N7 (SA12Z3): `near_R1`

The R1 near estimate (`s ≤ d - 2`, any matrix with `|M| ≤ MB`, no dissipation spill).  The tuple-wise
bound `sa12z3_idx_bound` is summed with the binomial weights, and `∫ W Y` is compared with the cell energies
of the neighbours `E` (`W = ∑_{k ∈ E} (χ_{z+k}^τ)²`).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `∫ W Y` is bounded by the sum of the neighbouring cell energies. -/
theorem sa12z3_e_le (m : ℕ) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d} {τ : ℝ}
    {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k)))) :
    ∫ x, sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x ≤
      ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := by
  have hint : ∀ k ∈ E, ∀ (r : ℕ) (γ : Fin r → Fin d),
      Integrable (fun x => (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv γ F x) ^ 2) volume := by
    intro k hk r γ
    have hc := (hω k hk).1
    have hcs := (hω k hk).2
    have hpd : Continuous (partialDeriv γ F) := (sa12z3_pd_contDiff_inf hF γ).continuous
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => (advCutoff χ Ψ τ (cellPt d (z + k)) x *
      partialDeriv γ F x) ^ 2) ((hc.mul hpd).pow 2)
      ((hcs.mul_right (f' := partialDeriv γ F)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hpt : ∀ x, sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x = ∑ k ∈ E, ∑ r ∈ Finset.range (m + 1),
      ∑ γ : Fin r → Fin d, (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv γ F x) ^ 2 := by
    intro x
    unfold sa12z3_W sa12z3_Y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ fun r _ => integrable_finsetSum _
    fun γ _ => hint k hk r γ)]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ fun γ _ => hint k hk r γ)]
  unfold cellEnergy jetSq
  refine Finset.sum_le_sum fun r _ => ?_
  rw [integral_finsetSum _ (fun γ _ => hint k hk r γ)]
  have h0 : 0 ≤ ∑ γ : Fin r → Fin d, ∫ x, (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv γ F x) ^ 2 :=
    Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hc : (1 : ℝ) ≤ (Nat.choose m r : ℝ) := by
    have : 1 ≤ Nat.choose m r := Nat.choose_pos (by
      have := Finset.mem_range.1 ‹r ∈ Finset.range (m + 1)›; omega)
    exact_mod_cast this
  exact le_mul_of_one_le_left h0 hc

end HRS.MH.AdjointRd.Phase2SA12Near
