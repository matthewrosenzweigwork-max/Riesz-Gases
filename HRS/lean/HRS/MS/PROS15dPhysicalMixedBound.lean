import HRS.MS.PROS15dPhysicalTiltBound
import HRS.MS.S21G2_K11b

/-!
# S15d: bilinear continuity of physical Gaussian observables under a square-integrable tilt

The same likelihood is used for both observables. This does not identify the
physical quadratic Wick variable with its spectral representation and is not
a proof of the frozen R26-T3.S15d contract.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_tilted_mixed_second_bound
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (f g : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (V : I.Ω → ℝ) (hV : AEMeasurable V I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) I.P) :
    |∫ ω, I.η f ω * I.η g ω ∂(r26t3_tilt I.P V)| ≤
      Real.sqrt ((∫ ω, Real.exp (-V ω) ∂I.P)⁻¹ *
        ((Real.sqrt 3 * ∫ x, f x ^ 2 ∂μ) *
          Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P))) *
      Real.sqrt ((∫ ω, Real.exp (-V ω) ∂I.P)⁻¹ *
        ((Real.sqrt 3 * ∫ x, g x ^ 2 ∂μ) *
          Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P))) := by
  letI := I.mΩ
  letI := I.prob
  letI : IsProbabilityMeasure (r26t3_tilt I.P V) :=
    r26t3_tilt_isProb I.P hV hExp1
  have hfT : MemLp (I.η f) 2 (r26t3_tilt I.P V) :=
    s15d_physical_first_chaos_tilt_L2 I f hf V hV hExp1 hExp2
  have hgT : MemLp (I.η g) 2 (r26t3_tilt I.P V) :=
    s15d_physical_first_chaos_tilt_L2 I g hg V hV hExp1 hExp2
  have hfb := s15d_physical_tilted_second_bound I f hf V hV hExp1 hExp2
  have hgb := s15d_physical_tilted_second_bound I g hg V hV hExp1 hExp2
  exact (s21g2_k11b_cs hfT hgT).trans
    (mul_le_mul (Real.sqrt_le_sqrt hfb) (Real.sqrt_le_sqrt hgb)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end HRS.MS.R26T3
