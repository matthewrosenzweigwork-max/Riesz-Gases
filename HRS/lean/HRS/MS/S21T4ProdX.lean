import HRS.MS.S21T4ProdW
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Tensor product of L² functions belongs to L² of a product measure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- For arbitrary Borel probability measures, rank-one separated kernels belong to
`L²(μ⊗μ)` and the norm identity holds exactly. -/
theorem s21t4_separated_kernel_memLp (f g : Euc d → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun z : Euc d × Euc d => f z.1 * g z.2) 2 (μ.prod μ) := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have hsm : AEStronglyMeasurable (fun z : Euc d × Euc d => f z.1 * g z.2)
      (μ.prod μ) :=
    (hf.aestronglyMeasurable.comp_fst.mul (hg.aestronglyMeasurable.comp_snd))
  apply (memLp_two_iff_integrable_sq hsm).2
  have h : Integrable (fun z : Euc d × Euc d => (f z.1 ^ 2) * (g z.2 ^ 2))
      (μ.prod μ) := hf2.mul_prod hg2
  simpa only [mul_pow] using h

theorem s21t4_separated_kernel_sq_integral (f g : Euc d → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z : Euc d × Euc d, (f z.1 * g z.2) ^ 2 ∂(μ.prod μ)) =
      (∫ x, f x ^ 2 ∂μ) * (∫ y, g y ^ 2 ∂μ) := by
  have h := integral_prod_mul (μ := μ) (ν := μ)
    (fun x => f x ^ 2) (fun y => g y ^ 2)
  simpa only [mul_pow] using h

end HRS.MS.R26T3
