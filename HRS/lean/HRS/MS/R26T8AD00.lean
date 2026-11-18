import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom
import HRS.MS.S82WA04
import HRS.MS.S82WQ1

/-!
# S8.2 observed-time layer, packet T8A.D00: normal-form and feature-orbit objects

Fresh names `r26t8a_*` for the objects of the Pro skeleton that are not in the merged tree.  The four objects that already
exist (`Phase2S82.correctedQ`, `zetaActual`, `correctedD` from S82WQ1 and `Phase2S82.configPoleEnvelope` from S82WA04) are
re-exported as `abbrev`s so that the merged results A04/A05 apply by unification (the Pro D00 text would have made new,
unrelated constants).  `FeatureOrbits` has the field `exists` of the skeleton renamed `exists_solution`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

abbrev r26t8a_configPoleEnvelope {d N : ℕ} (M : ℝ) (X : EucConfig d N) : ℝ :=
  Phase2S82.configPoleEnvelope M X

abbrev r26t8a_correctedQ {d N : ℕ} (a beta : ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) :
    EucConfig d N → ℝ :=
  Phase2S82.correctedQ a beta Psi f

abbrev r26t8a_zetaActual {d N : ℕ} (a beta : ℝ) (f : Euc d → ℝ) : EucConfig d N → ℝ :=
  Phase2S82.zetaActual a beta f

abbrev r26t8a_correctedD {d N : ℕ} (a beta : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) :
    EucConfig d N → ℝ :=
  Phase2S82.correctedD a beta rho Psi f

def r26t8a_genPower {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (j : ℕ) (f : Euc d → ℝ) : Euc d → ℝ :=
  Nat.rec f (fun _ g => HRS.Whole.projGeneratorW C mu 0 g) j

def r26t8a_projectedOrbit {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (v : ℝ) (f : Euc d → ℝ) : Euc d → ℝ :=
  HRS.Whole.projMean mu (propagatorW C 0 v f)

/-- The exact feature data consumed by the normal-form path argument.  Only positive-order spatial norms decay. -/
structure r26t8a_FeatureOrbits (d : ℕ) (a beta m C c : ℝ) (rho : Euc d → ℝ) : Prop where
  exists_solution : ∀ alpha : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
    ∃ f, IsClassicalAdjointW (critCoeff d a beta rho) t (oscTestFun m alpha) f
  shift : ∀ alpha : MultiIndex d, ∀ r t : ℝ, 0 ≤ r → r ≤ t →
    propagatorW (critCoeff d a beta rho) r t (oscTestFun m alpha) =
      propagatorW (critCoeff d a beta rho) 0 (t - r) (oscTestFun m alpha)
  bound : ∀ alpha : MultiIndex d, ∀ v : ℝ, 0 ≤ v → ∀ j : ℕ, j ≤ 2 →
    TestBound (testOrder d)
      (C * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c * v))
      (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
        (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)))
  continuity : ∀ alpha : MultiIndex d, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun v => testSizeE (testOrder d)
      (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
        (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)) -
       r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
        (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) t (oscTestFun m alpha))))
      (𝓝[Set.Ici 0] t) (𝓝 0)
  derivative : ∀ alpha : MultiIndex d, ∀ j : ℕ, j ≤ 1 →
    ∀ k : ℕ, k ≤ testOrder d → ∀ t : ℝ, 0 ≤ t → ∀ x,
      HasDerivWithinAt (fun v => iteratedFDeriv ℝ k
        (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha))) x)
        (iteratedFDeriv ℝ k
          (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (j + 1)
            (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) t (oscTestFun m alpha))) x)
        (Set.Ici 0) t

/-- the abbreviations are literally the merged constants (so merged A04/A05 apply) -/
theorem r26t8a_correctedQ_eq {d N : ℕ} (a beta : ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) :
    r26t8a_correctedQ (N := N) a beta Psi f = Phase2S82.correctedQ a beta Psi f := rfl

end HRS.MS.R26T8A

end
