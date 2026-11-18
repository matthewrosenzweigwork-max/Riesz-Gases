import HRS.MS.PROS15dPhysicalTiltBound

/-!
# R26-T3.S15d: spatial L2 convergence transfers to tilted first-chaos L2

For any fixed square-integrable exponential likelihood, convergence of the
original physical spatial test functions in L2 implies L2 convergence of
their actual first-chaos observables under the tilted probability measure.
This directly handles arbitrary L2 spectral projections without regularity
assumptions on eigenfunctions.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_tilted_second_tendsto_of_spatial_second
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (V : I.Ω → ℝ) (hV : AEMeasurable V I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) I.P)
    (f : ℕ → HRS.Euc d → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (hSpatial : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, I.η (f n) ω ^ 2 ∂(r26t3_tilt I.P V)) atTop (𝓝 0) := by
  letI := I.mΩ
  letI := I.prob
  have hBound : ∀ n,
      ∫ ω, I.η (f n) ω ^ 2 ∂(r26t3_tilt I.P V) ≤
        (∫ ω, Real.exp (-V ω) ∂I.P)⁻¹ *
          ((Real.sqrt 3 * ∫ x, f n x ^ 2 ∂μ) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P)) :=
    fun n => s15d_physical_tilted_second_bound I (f n) (hf n) V hV hExp1 hExp2
  have htend : Tendsto (fun n =>
        (∫ ω, Real.exp (-V ω) ∂I.P)⁻¹ *
          ((Real.sqrt 3 * ∫ x, f n x ^ 2 ∂μ) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P))) atTop (𝓝 0) := by
    convert (((hSpatial.const_mul (Real.sqrt 3)).mul_const
      (Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P))).const_mul
      ((∫ ω, Real.exp (-V ω) ∂I.P)⁻¹)) using 1 <;> ring
  exact squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hBound htend

end HRS.MS.R26T3
