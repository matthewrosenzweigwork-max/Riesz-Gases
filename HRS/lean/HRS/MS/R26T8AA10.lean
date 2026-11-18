import HRS.MS.S82WA05
import HRS.MS.R26T8AD00
import HRS.MS.R26T8AA02
import HRS.MS.R26T8AM07
import HRS.MS.R26T8AM13

/-!
# S8.2 T8A A10: `r26t8a_normal_form_bound` (Pro contract, verbatim)
By the D00 abbreviations the statement is the merged, fully proved `Phase2S82.normal_form_bound` (S82WA05), whose proof uses the
merged `weighted_pair_moments`, `weighted_repeated_pair_moments` (= M07), `canonical_triple_and_bounds` (= A02) and
`weighted_triple_moments` (= M13).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem _root_.HRS.MS.R26T8A.r26t8a_normal_form_bound (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
      ∀ f : Euc d → ℝ, ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      TestBound (testOrder d) A f →
      PairCorrector a beta rho M B f (Psi f) →
      MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) →
      eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal B →
      ∀ N : ℕ, 2 ≤ N →
        GeneratorClosure a beta (HRS.MS.R26T8A.r26t8a_correctedQ (N := N) a beta Psi f)
          (fun X => -scalarForcing a beta rho f X + HRS.MS.R26T8A.r26t8a_correctedD a beta rho Psi f X) ∧
        MemLp (HRS.MS.R26T8A.r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ∧
        (∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          scalarForcing a beta rho f X =
            -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
              (HRS.MS.R26T8A.r26t8a_correctedQ a beta Psi f) X + HRS.MS.R26T8A.r26t8a_correctedD a beta rho Psi f X) ∧
        eLpNorm (HRS.MS.R26T8A.r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) +
          (∫⁻ X, ∑ i, ‖configGrad (HRS.MS.R26T8A.r26t8a_correctedQ a beta Psi f) X i‖ₑ ^ 2
            ∂canonicalP d N a beta) ^ (1 / 2 : ℝ) +
          eLpNorm (HRS.MS.R26T8A.r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * (A + B) * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
  normal_form_bound d hd a beta M C0 C1 ha hbeta hM q hq

end HRS.MS.Phase2S82
