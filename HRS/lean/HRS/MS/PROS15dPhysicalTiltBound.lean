import HRS.MS.PROS15dPhysicalFourthBound

/-!
# R26-T3.S15d: quantitative continuity of arbitrary physical test observables

Unlike the spectral-coordinate bound, this controls the actual ProductGaussian
field applied to any spatial L2 test f, under any square-integrable exponential
tilt, by the original spatial L2 norm. A direct consequence is extension of
finite-dimensional spectral Gaussian laws to the full spatial test class once
the physical Wick quadratic is identified with its spectral representative.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_tilted_second_bound
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ)
    (V : I.Ω → ℝ) (hV : AEMeasurable V I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) I.P) :
    ∫ ω, I.η f ω ^ 2 ∂(r26t3_tilt I.P V) ≤
      (∫ ω, Real.exp (-V ω) ∂I.P)⁻¹ *
        ((Real.sqrt 3 * ∫ x, f x ^ 2 ∂μ) *
          Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂I.P)) := by
  letI := I.mΩ
  letI := I.prob
  have hfourth := s15d_physical_fourth_le_three_spatial_second_sq I f hf
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hsqrt : Real.sqrt (∫ ω, I.η f ω ^ 4 ∂I.P) ≤
      Real.sqrt 3 * ∫ x, f x ^ 2 ∂μ := by
    calc
      Real.sqrt (∫ ω, I.η f ω ^ 4 ∂I.P) ≤
          Real.sqrt (3 * (∫ x, f x ^ 2 ∂μ) ^ 2) :=
            Real.sqrt_le_sqrt hfourth
      _ = Real.sqrt 3 * ∫ x, f x ^ 2 ∂μ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hnonneg]
  have hbase := s15d_tilted_second_moment_bound hV hExp1 hExp2
    (s15d_physical_first_chaos_L4 I f hf)
  exact hbase.trans (by gcongr)

end HRS.MS.R26T3
