import HRS.MS.R26T8AA01v

/-!
# S8.2 T8A A01: `r26t8a_triple_zero_row` (Pro contract, verbatim)
Integrability: A01e; vanishing of the integral: A01v.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_triple_zero_row (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : Euc d → ℝ) (A : ℝ) (hA : 0 ≤ A) (Q : Euc d → Euc d → ℝ)
    (hQ : PairCorrector a beta rho M A f Q) :
    ∀ x y, x ≠ y → Integrable (fun z => tripleG (critCoeff d a beta rho) rho Q x y z)
      (HRS.Whole.withDensityReal rho) ∧
      ∫ z, tripleG (critCoeff d a beta rho) rho Q x y z ∂HRS.Whole.withDensityReal rho = 0 := by
  intro x y hxy
  exact ⟨r26t8a_a01_integrable d hd a beta M ha hbeta hM hrho hA hQ hxy,
    r26t8a_a01_zero d hd a beta M ha hbeta hM hrho hA hQ hxy⟩

end HRS.MS.R26T8A
