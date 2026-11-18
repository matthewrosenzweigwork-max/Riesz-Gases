import HRS.MS.PROS15dTiltBound

/-!
# R26-T3.S15d: transfer of L4 convergence to tilted L2 convergence

The square-integrability of the exponential density, together with the
quantitative moment bound, allows L4(P) approximations of Gaussian first
chaos observables to converge in L2 under the tilted probability law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_tilted_L2_tendsto_of_L4
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → ℝ} (hV : AEMeasurable V P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (F : ℕ → Ω → ℝ) (hF4 : ∀ n, MemLp (F n) 4 P)
    (h4 : Tendsto (fun n => ∫ ω, F n ω ^ 4 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂(r26t3_tilt P V)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (∫ ω, F n ω ^ 4 ∂P)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp h4
  have hbound : ∀ n,
      ∫ ω, F n ω ^ 2 ∂(r26t3_tilt P V) ≤
        (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
          (Real.sqrt (∫ ω, F n ω ^ 4 ∂P) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P)) :=
    fun n => s15d_tilted_second_moment_bound hV hExp1 hExp2 (hF4 n)
  have hr : Tendsto (fun n =>
        (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
          (Real.sqrt (∫ ω, F n ω ^ 4 ∂P) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P))) atTop (𝓝 0) := by
    simpa using ((hs.mul_const (Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P))).const_mul
      ((∫ ω, Real.exp (-V ω) ∂P)⁻¹))
  exact squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound hr

end HRS.MS.R26T3
