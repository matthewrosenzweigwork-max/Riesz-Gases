import HRS.MS.S21T4ProdAX

/-! S13: the genuine Wick-continuity domain is closed under finite kernel families. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_kernel_family_KOK {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ) (hh : ∀ i, S94KOK μ (h i))
    (α : Fin m → ℝ) :
    S94KOK μ (fun x y => ∑ i, α i * h i x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hh i).meas
  · intro x y
    exact Finset.sum_congr rfl fun i _ => by rw [(hh i).symm x y]
  · exact memLp_finsetSum _ fun i _ => ((hh i).memLp).const_mul (α i)
  · intro x
    exact integrable_finsetSum _ fun i _ => ((hh i).row x).const_mul (α i)
  · have hm : Integrable (fun x => ∑ i : Fin m,
        α i * ∫ y, h i x y ∂μ) μ :=
      integrable_finsetSum _ fun i _ => ((hh i).hc).const_mul (α i)
    have he : (fun x => ∫ y, (∑ i : Fin m, α i * h i x y) ∂μ) =
        (fun x => ∑ i : Fin m, α i * ∫ y, h i x y ∂μ) := by
      funext x
      exact s21t4_kernel_family_row_integral h hh α x
    rw [he]
    exact hm

end HRS.MS.R26T3
