import HRS.Prob.Gaussian

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- The quantitative sixth-moment contract, with the constant chosen before the law. -/
def fp81s21_GaussSixthStatement : Prop :=
  ∃ C6 : ℝ, 0 ≤ C6 ∧ ∀ μ : Measure B, IsProbabilityMeasure μ →
    HRS.IsCenteredGaussian μ → ∀ B4 : ℝ, 0 ≤ B4 →
    Integrable (fun x : B => ‖x‖ ^ 4) μ →
    (∫ x, ‖x‖ ^ 4 ∂μ) ≤ B4 →
    Integrable (fun x : B => ‖x‖ ^ 6) μ ∧
    (∫ x, ‖x‖ ^ 6 ∂μ) ≤ C6 * (1 + B4) ^ 6

/-- Every Gaussian law on a separable Banach space has a finite sixth moment. -/
theorem fp81s21_gauss_sixth_integrable (μ : Measure B)
    (hμ : HRS.IsCenteredGaussian μ) :
    Integrable (fun x : B => ‖x‖ ^ 6) μ := by
  letI : ProbabilityTheory.IsGaussian μ := hμ.1
  exact (ProbabilityTheory.IsGaussian.memLp_id μ 6 (by norm_num)).integrable_norm_pow
    (by norm_num)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_gauss_sixth_integrable
