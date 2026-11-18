import HRS.MS.SA12X3C7C9

/-!
# S.A.12 C7 (SA12X3), part C10 (7C): Schur reindexing from coarse cosets to the fine lattice

Given Schur matrices `K r q y` (residue `r ∈ [0,κ)^d`, coarse source `q`, flowed-cube index `y`) with row bound and weighted column
bound, `Kfin z z'' = ∑_{ε∈{0,1}^d} K (z mod κ) (z / κ) (z'' - ε)` has the same type of bounds on the fine lattice, and
`∑ z'' Kfin z z'' g z'' = ∑ y K r q y ∑_ε g (y+ε)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

/-- Residue vectors `[0,κ)^d`. -/
def sa12x3_Rset (d : ℕ) (κ : ℤ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) κ

def sa12x3_Kfin (κ : ℤ) (K : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) (z z'' : Fin d → ℤ) : ℝ≥0 :=
  ∑ ε : Fin d → Fin 2, K (fun i => z i % κ) (fun i => z i / κ) (z'' - fun i => ((ε i : ℕ) : ℤ))

theorem sa12x3_res_mem {κ : ℤ} (hκ : 1 ≤ κ) (z : Fin d → ℤ) : (fun i => z i % κ) ∈ sa12x3_Rset d κ := by
  unfold sa12x3_Rset
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Ico]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

theorem sa12x3_Kfin_mass {κ : ℤ} (K : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) (z : Fin d → ℤ)
    (g : (Fin d → ℤ) → ℝ≥0∞) :
    ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) * g z'' =
      ∑' y, (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞) *
        ∑ ε : Fin d → Fin 2, g (y + fun i => ((ε i : ℕ) : ℤ)) := by
  unfold sa12x3_Kfin
  simp_rw [ENNReal.coe_finset_sum, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun ε _ => ENNReal.summable)]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun ε _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← (Equiv.subRight (fun i => ((ε i : ℕ) : ℤ))).tsum_eq
    (fun y => (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞) * g (y + fun i => ((ε i : ℕ) : ℤ)))]
  refine tsum_congr fun z'' => ?_
  simp [Equiv.subRight_apply]

end HRS.MH.AdjointRd.Phase2SA12Near
