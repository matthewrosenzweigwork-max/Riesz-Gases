import HRS.MS.PROS15dPhysicalGaussianLaw

/-!
# R26-T3.S15d: exact fourth moment for every physical Gaussian observable

This upgrades the mere L4 integrability of the arbitrary physical first chaos
to an exact Wick fourth moment relation. Its covariance under the original
Gaussian law is given by the ProductGaussian covariance identity.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_fourth_eq_three_sq_second
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    ∫ ω, I.η f ω ^ 4 ∂I.P = 3 * (∫ ω, I.η f ω ^ 2 ∂I.P) ^ 2 := by
  letI := I.mΩ
  letI := I.prob
  obtain ⟨v, hLaw⟩ := s15d_physical_centered_gaussian_law I f hf
  have hsecond : ∫ ω, I.η f ω ^ 2 ∂I.P = (v : ℝ) :=
    s21g2_s11a_second (I.meas f hf).aemeasurable hLaw
  calc
    ∫ ω, I.η f ω ^ 4 ∂I.P =
        ∫ x : ℝ, x ^ 4 ∂(I.P.map (I.η f)) := by
          exact (integral_map (I.meas f hf).aemeasurable
            (measurable_id.pow_const 4).aestronglyMeasurable).symm
    _ = 3 * (v : ℝ) ^ 2 := by
      rw [hLaw, integral_pow_four_gaussianReal_zero]
    _ = 3 * (∫ ω, I.η f ω ^ 2 ∂I.P) ^ 2 := by rw [hsecond]

end HRS.MS.R26T3
