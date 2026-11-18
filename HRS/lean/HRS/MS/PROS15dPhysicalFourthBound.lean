import HRS.MS.PROS15dPhysicalFourth

/-!
# R26-T3.S15d: quantitative fourth-moment bound of the physical isonormal field

This bounds the fourth moment by three times the square of the physical
spatial L2 norm. It is the precise hypercontractive estimate required for
Gaussian spectral projections (before and after the square-integrable tilt).
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_fourth_le_three_spatial_second_sq
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    ∫ ω, I.η f ω ^ 4 ∂I.P ≤ 3 * (∫ x, f x ^ 2 ∂μ) ^ 2 := by
  letI := I.mΩ
  letI := I.prob
  rw [s15d_physical_fourth_eq_three_sq_second I f hf,
    show (∫ ω, I.η f ω ^ 2 ∂I.P) =
      (∫ x, HRS.Whole.projMean μ f x ^ 2 ∂μ) from by
        simpa only [pow_two] using I.covariance f f hf hf]
  have hVar : ∫ x, HRS.Whole.projMean μ f x ^ 2 ∂μ =
      Var[f; μ] := by
    rw [variance_eq_integral hf.aemeasurable]
    rfl
  rw [hVar]
  have hLower : 0 ≤ Var[f; μ] := variance_nonneg f μ
  have hUpper : Var[f; μ] ≤ ∫ x, f x ^ 2 ∂μ :=
    variance_le_expectation_sq hf.aestronglyMeasurable
  have hRaw : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  gcongr

end HRS.MS.R26T3
