import HRS.MS.S82QR07

/-!
# S8.2 T8A M13: `r26t8a_weighted_triple_moments` (Pro contract, verbatim)
Identical to the merged, fully proved `Phase2S82.weighted_triple_moments`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem _root_.HRS.MS.R26T8A.r26t8a_weighted_triple_moments (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ G : Euc d → Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2) →
      CanonicalTriple (HRS.Whole.withDensityReal rho) G →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        |G x y z| ≤ A * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * triplePole x y z) →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum G X) 2 (canonicalP d N a beta) ∧
        evariance (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum G X) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2) :=
  weighted_triple_moments d hd a beta M C0 C1 ha hbeta hM q hq

end HRS.MS.Phase2S82
