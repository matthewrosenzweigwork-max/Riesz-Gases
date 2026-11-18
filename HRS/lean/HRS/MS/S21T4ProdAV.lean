import HRS.MS.S21T4ProdAU
import HRS.MS.WrRowAux1

/-! S13 finite families: stability of the singular envelope under scalar projection. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ}

theorem s21t4_weighted_kernel_bound {m : ℕ} (s : ℝ)
    (B α : Fin m → ℝ) (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, IsBoundedPairKernel s (B i) (h i)) :
    IsBoundedPairKernel s (∑ i, |α i| * |B i|)
      (fun x y => ∑ i, α i * h i x y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (hh i).measurable
  · intro x y
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hh i).symm x y]
  · intro x y hxy
    let W : ℝ := 1 + rieszWeight s (x - y)
    have hW : 0 ≤ W := by
      dsimp [W]
      linarith [HRS.MS.Wr.wr3_rieszWeight_nonneg s (x - y)]
    calc
      |∑ i : Fin m, α i * h i x y| ≤ ∑ i, |α i * h i x y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, (|α i| * |B i|) * W := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have h1 : |h i x y| ≤ B i * W := (hh i).bound x y hxy
        calc
          |α i| * |h i x y| ≤ |α i| * (B i * W) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ |α i| * (|B i| * W) := by
            gcongr
            exact le_abs_self _
          _ = (|α i| * |B i|) * W := by ring
      _ = (∑ i : Fin m, |α i| * |B i|) * W := by
        rw [Finset.sum_mul]

end HRS.MS.R26T3
