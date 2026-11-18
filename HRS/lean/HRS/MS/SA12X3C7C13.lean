import HRS.MS.SA12X3C7C12
import HRS.MH.AdjRdT7

/-!
# S.A.12 C7 (SA12X3), part C13 (7C): the fine-lattice Schur kernel of the far term

From `screened_far_periodic_gen` (every kernel order `1 ≤ n ≤ m+1`, finitely many cosets of the fine lattice) we build one kernel
`Kfin` with row bound and weighted column bound and the `L²` bound of every `w_z T_z` by the cell masses.
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

def sa12x3_e (d : ℕ) (κ : ℤ) (r : Fin d → ℤ) : Euc d := WithLp.toLp 2 fun i => (r i : ℝ) / κ

theorem sa12x3_cellPt_dec {κ : ℤ} (hκ : (κ : ℝ) = ⌈Real.sqrt d⌉) (hκ1 : 1 ≤ κ) (z : Fin d → ℤ) :
    cellPt d z = latticePt (fun i => z i / κ) + sa12x3_e d κ (fun i => z i % κ) := by
  ext i
  have hκ1R : (1 : ℝ) ≤ κ := by exact_mod_cast hκ1
  have hκ0 : (κ : ℝ) ≠ 0 := by linarith
  have h := Int.mul_ediv_add_emod (z i) κ
  have h' : ((z i : ℤ) : ℝ) = κ * ((z i / κ : ℤ) : ℝ) + ((z i % κ : ℤ) : ℝ) := by exact_mod_cast h.symm
  simp only [cellPt, latticePt, sa12x3_e, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, ← hκ]
  rw [h']
  field_simp

theorem sa12x3_e_bounds {κ : ℤ} (hκ1 : 1 ≤ κ) {r : Fin d → ℤ} (hr : r ∈ sa12x3_Rset d κ) :
    (∀ i, 0 ≤ sa12x3_e d κ r i) ∧ (∀ i, sa12x3_e d κ r i < 1) ∧ ‖sa12x3_e d κ r‖ ≤ Real.sqrt d := by
  have hκ1R : (1 : ℝ) ≤ κ := by exact_mod_cast hκ1
  have hκR : (0 : ℝ) < κ := by linarith
  have hri : ∀ i, 0 ≤ r i ∧ r i < κ := fun i => by
    have := (Fintype.mem_piFinset.1 hr) i
    exact Finset.mem_Ico.1 this
  have h0 : ∀ i, 0 ≤ sa12x3_e d κ r i := fun i => by
    show 0 ≤ (r i : ℝ) / κ
    exact div_nonneg (Int.cast_nonneg (hri i).1) hκR.le
  have h1 : ∀ i, sa12x3_e d κ r i < 1 := fun i => by
    show (r i : ℝ) / κ < 1
    rw [div_lt_one hκR]; exact_mod_cast (hri i).2
  refine ⟨h0, h1, ?_⟩
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖sa12x3_e d κ r i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 i)]
        nlinarith [h0 i, h1 i]
    _ = d := by simp

end HRS.MH.AdjointRd.Phase2SA12Near
