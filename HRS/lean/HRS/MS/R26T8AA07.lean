import HRS.MS.R26T8AA02
import HRS.MS.CritForceNF1

/-!
# S8.2 T8A A07: `r26t8a_deleted_canonical_identity` (Pro contract, verbatim)
This is the merged `s82n_deleted_canonical_identity`; `pairStatistic` and `s82n_pairStatistic` agree by unfolding.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_deleted_canonical_identity
    (d N : ℕ) (hN : 1 ≤ N) (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (h : Euc d → Euc d → ℝ) (hsym : ∀ x y, h x y = h y x)
    (hrow : ∀ x, Integrable (h x) mu)
    (hint : Integrable (Function.uncurry h) (mu.prod mu))
    (X : EucConfig d N) :
    (Real.sqrt N / 2) * centeredPairFunctional h X mu -
      HRS.MS.Phase2S82.pairStatistic (fun x y => (1 / 2) * r2CenterKernel mu h x y) X =
        -(N : ℝ) ^ (-(3 / 2 : ℝ)) * (∑ i, ∫ y, h (X i) y ∂mu) +
          (∫ x, ∫ y, h x y ∂mu ∂mu) / (2 * Real.sqrt N) :=
  HRS.MS.S82N.s82n_deleted_canonical_identity d N hN mu h hsym hrow hint X

end HRS.MS.R26T8A
