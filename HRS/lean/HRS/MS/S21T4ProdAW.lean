import HRS.MS.S21T4ProdAV
import HRS.MS.R2ChaosAux56

/-! S13: Bochner-safe linearity of finite kernel family means. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_kernel_family_row_integral {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, S94KOK μ (h i)) (α : Fin m → ℝ) (x : Euc d) :
    (∫ y, ∑ k : Fin m, α k * h k x y ∂μ) =
      ∑ k : Fin m, α k * ∫ y, h k x y ∂μ := by
  rw [integral_finset_sum _ fun k _ => ((hh k).row x).const_mul (α k)]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

theorem s21t4_kernel_family_double_integral {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, S94KOK μ (h i)) (α : Fin m → ℝ) :
    (∫ x, ∫ y, ∑ k : Fin m, α k * h k x y ∂μ ∂μ) =
      ∑ k : Fin m, α k * ∫ x, ∫ y, h k x y ∂μ ∂μ := by
  have hrow : (fun x => ∫ y, ∑ k : Fin m, α k * h k x y ∂μ) =
      (fun x => ∑ k : Fin m, α k * ∫ y, h k x y ∂μ) := by
    funext x
    exact s21t4_kernel_family_row_integral h hh α x
  rw [hrow]
  rw [integral_finset_sum _ fun k _ => ((hh k).hc).const_mul (α k)]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

end HRS.MS.R26T3
