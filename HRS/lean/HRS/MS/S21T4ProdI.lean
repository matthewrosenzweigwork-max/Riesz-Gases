import HRS.MS.S21T4ProdH

/-! S13: uniform particle Chebyshev estimate after actual L² membership. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

/-- A quantitative probability tail, uniform in N, for the centered pair statistic.
The integral bound is applied only after proving the statistic genuinely belongs to L². -/
theorem s21t4_s13_tail {N : ℕ} (hN : 2 ≤ N)
    (h : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) (ε : ℝ) :
    ε ^ 2 * (Measure.pi fun _ : Fin N => μ).real
      {X : EucConfig d N | ε ^ 2 ≤
        ((N : ℝ) * pairEnergy h X μ +
          (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ) ^ 2} ≤
      18 * ∫ z : Euc d × Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let Z : EucConfig d N → ℝ := fun X =>
    (N : ℝ) * pairEnergy h X μ + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ
  have hZ : MemLp Z 2 ν := s21t4_s13_particle_memLp μ hN h hm hs
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := ν) (f := fun X => (Z X) ^ 2)
      (Filter.Eventually.of_forall fun X => sq_nonneg (Z X))
      hZ.integrable_sq (ε ^ 2)
  exact hmarkov.trans (s21l_s13_variance μ hN h hm hs)

end HRS.MS.R26T3
