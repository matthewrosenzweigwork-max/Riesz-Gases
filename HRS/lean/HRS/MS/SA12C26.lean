import HRS.MS.SA12C25

/-!
# S.A.12(c), packet E7.04 (part 10): continuity of the inner average and algebraic helpers
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- `c ↦ ∫ x, F c x` is continuous for a continuous family supported in `|x - c| ≤ R`. -/
theorem sa12c_avg_inner_cont {F : Euc d → Euc d → ℝ} (hc : Continuous (Function.uncurry F)) {R : ℝ}
    (hsupp : ∀ c x, R < ‖x - c‖ → F c x = 0) : Continuous (fun c => ∫ x, F c x) := by
  have h1 : ∀ c, ∫ x, F c x = ∫ v in Metric.closedBall (0 : Euc d) R, F c (c + v) := by
    intro c
    rw [← integral_add_left_eq_self (fun x => F c x) c]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_
    apply hsupp
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    simpa using hv
  simp_rw [h1]
  exact continuous_parametric_integral_of_continuous (f := fun c v => F c (c + v))
    (hc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))) (isCompact_closedBall _ _)

/-- Cauchy-Schwarz for a finite double sum with bounded coefficients. -/
theorem sa12c_matsum_sq {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) (h : Fin d → Fin d → ℝ) :
    (∑ i : Fin d, ∑ j : Fin d, M j i * h i j) ^ 2 ≤ ((d : ℝ) ^ 2 * MB ^ 2) * ∑ i : Fin d, ∑ j : Fin d, h i j ^ 2 := by
  have hsum : (∑ i : Fin d, ∑ j : Fin d, M j i * h i j) = ∑ p : Fin d × Fin d, M p.2 p.1 * h p.1 p.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun p => M p.2 p.1) (fun p => h p.1 p.2)
  have hM2 : ∑ p : Fin d × Fin d, M p.2 p.1 ^ 2 ≤ (d : ℝ) ^ 2 * MB ^ 2 := by
    calc ∑ p : Fin d × Fin d, M p.2 p.1 ^ 2 ≤ ∑ _p : Fin d × Fin d, MB ^ 2 := by
          refine Finset.sum_le_sum fun p _ => ?_
          have := hM p.2 p.1
          exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
      _ = (d : ℝ) ^ 2 * MB ^ 2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hsq : ∑ p : Fin d × Fin d, h p.1 p.2 ^ 2 = ∑ i : Fin d, ∑ j : Fin d, h i j ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsum]
  refine hcs.trans ?_
  rw [hsq]
  exact mul_le_mul_of_nonneg_right hM2 (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

end HRS.MH.AdjointRd.Phase2SA12C
