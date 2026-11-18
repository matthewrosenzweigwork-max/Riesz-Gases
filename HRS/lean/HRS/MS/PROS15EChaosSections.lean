import HRS.MS.PROS15EChaosTiltContinuity
import HRS.MS.S21H2_S15c

/-!
# Exact second-chaos membership for finite Hilbert--Schmidt spectral sections

The finite diagonal Wiener quadratics used in the physical spectral tilt are
honest members of the closed second Gaussian chaos for the same underlying
standard Gaussian sequence. This is a premise for applying the quantitative
tilted-L2 transfer to their infinite-dimensional limit.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_diagonal_sections_second_chaos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (n : ℕ) :
    InQ2 hξ (s21h2_s15c_Qn ξ lam n) := by
  have hterm : ∀ j ∈ Finset.range n,
      InQ2 hξ (fun ω => lam j * (ξ j ω ^ 2 - 1)) := by
    intro j hj
    have hbase : InQ2 hξ (fun ω => ξ j ω ^ 2 - 1) := by
      simpa [pow_two] using InQ2_term hξ j j
    exact InQ2.const_mul (lam j) hbase
  have hsum : InQ2 hξ (fun ω =>
      ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1)) :=
    InQ2.sum (Finset.range n) hterm
  have hhalf := InQ2.const_mul (1 / 2 : ℝ) hsum
  change InQ2 hξ (fun ω => (1 / 2 : ℝ) *
      ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1))
  exact hhalf

#print axioms s15e_diagonal_sections_second_chaos
end HRS.MS.R26T3
