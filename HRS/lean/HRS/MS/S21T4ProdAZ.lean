import HRS.MS.S21T4ProdAY

/-! S13: double centering commutes with finite linear combinations of integrable
symmetric product kernels, including for atomic reference measures. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_center_family_linear {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, S94KOK μ (h i))
    (α : Fin m → ℝ) (x y : Euc d) :
    r2CenterKernel μ (fun x y => ∑ i, α i * h i x y) x y =
      ∑ i : Fin m, α i * r2CenterKernel μ (h i) x y := by
  have hcol :
      (∫ x', ∑ i : Fin m, α i * h i x' y ∂μ) =
        ∑ i : Fin m, α i * ∫ x', h i x' y ∂μ := by
    rw [integral_finset_sum _ fun i _ => ((hh i).col y).const_mul (α i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  unfold r2CenterKernel
  rw [s21t4_kernel_family_row_integral h hh α x, hcol,
    s21t4_kernel_family_double_integral h hh α]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

end HRS.MS.R26T3
