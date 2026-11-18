import HRS.MS.SA12X3C7C14

/-!
# S.A.12 C7 (SA12X3), part C15 (7C): the far term `L²` bound with a fine-lattice Schur kernel
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction
  HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x3_Ksum_row {ι : Type*} [Fintype ι] (Kc : ι → (Fin d → ℤ) → ℝ≥0) (Cc : ι → ℝ)
    (h : ∀ i, ∑' y, (Kc i y : ℝ≥0∞) ≤ ENNReal.ofReal (Cc i)) :
    ∑' y, ((∑ i, Kc i y : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (∑ i, max (Cc i) 0) := by
  simp_rw [ENNReal.coe_finset_sum]
  rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => le_max_right _ _)]
  exact Finset.sum_le_sum fun i _ => (h i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem sa12x3_Ksum_col {ι : Type*} [Fintype ι] (Kc : ι → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) (Cc : ι → ℝ)
    (y : Fin d → ℤ)
    (h : ∀ i, ∑' q, ENNReal.ofReal (cellWeight d q) * (Kc i q y : ℝ≥0∞) ≤
      ENNReal.ofReal (Cc i) * ENNReal.ofReal (cellWeight d y)) :
    ∑' q, ENNReal.ofReal (cellWeight d q) * ((∑ i, Kc i q y : ℝ≥0) : ℝ≥0∞) ≤
      ENNReal.ofReal (∑ i, max (Cc i) 0) * ENNReal.ofReal (cellWeight d y) := by
  simp_rw [ENNReal.coe_finset_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => le_max_right _ _), Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => (h i).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)

end HRS.MH.AdjointRd.Phase2SA12Near
