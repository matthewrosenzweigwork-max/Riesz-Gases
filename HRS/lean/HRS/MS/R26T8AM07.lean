import HRS.MS.S82TFinal

/-!
# S8.2 T8A M07: `r26t8a_weighted_repeated_pair_moments` (Pro contract, verbatim)
Identical to the merged, fully proved `Phase2S82.weighted_repeated_pair_moments`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem _root_.HRS.MS.R26T8A.r26t8a_weighted_repeated_pair_moments (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (pairStatistic (N := N) (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q))
          2 (canonicalP d N a beta) ∧
        MemLp (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSum (repeatedB rho Q) X) 2 (canonicalP d N a beta) ∧
        evariance (pairStatistic (N := N)
          (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q)) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 * logN N / N) ∧
        evariance (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSum (repeatedB rho Q) X) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 / N) :=
  weighted_repeated_pair_moments d hd a beta M C0 C1 ha hbeta hM q hq

end HRS.MS.Phase2S82
