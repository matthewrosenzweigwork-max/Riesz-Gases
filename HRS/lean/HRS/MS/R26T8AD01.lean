import HRS.MS.R26T8AD00
import HRS.MS.S81R_Main

/-!
# S8.2 observed-time layer, packet T8A.D01: observed-time and normal-family definitions

`r26t8a_ReversibleWindows` is an abbrev of the merged `S81R.ReversibleWindows`, so `s81r_canonical_reversible_windows`
(S8.2 O04) supplies it.  `r26t8a_correctorNoise` is the Pro D01 version (noise zero on collisions and off `[0,b]`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

def r26t8a_scalarSupSq {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (T : ℝ) (Y : ℝ → Omega → ℝ) : ℝ≥0∞ :=
  ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ∂P

def r26t8a_clipIntegrand {Omega I : Type*} (a b : ℝ)
    (H : ℝ → Omega → I → ℝ) : ℝ → Omega → I → ℝ :=
  fun r w i => if r ∈ Set.Icc a b then H r w i else 0

def r26t8a_itoEnergy {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) (H : ℝ → Omega → I → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, (∫⁻ r in Set.Icc a b, ∑ i, ‖H r w i‖ₑ ^ 2) ∂P

abbrev r26t8a_ReversibleWindows {d N : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : ℝ≥0 → Omega → EucConfig d N) : Prop :=
  HRS.MS.S81R.ReversibleWindows P X

structure r26t8a_NormalFormFamily (d : ℕ) (a beta M C : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) : Prop where
  linear : ∀ f g, ∀ A B : ℝ, TestBound (testOrder d) A f →
    TestBound (testOrder d) B g → ∀ c : ℝ, Psi (f + c • g) = Psi f + c • Psi g
  constants : ∀ c : ℝ, Psi (fun _ => c) = 0
  corrector : ∀ f, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
    PairCorrector a beta rho M (C * A) f (Psi f)
  domain : ∀ N : ℕ, 2 ≤ N → ∀ f, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
    GeneratorClosure a beta (r26t8a_correctedQ (N := N) a beta Psi f)
      (fun X => -scalarForcing a beta rho f X + r26t8a_correctedD a beta rho Psi f X)
  identity : ∀ N : ℕ, 2 ≤ N → ∀ f, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      scalarForcing a beta rho f X =
        -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
          (r26t8a_correctedQ a beta Psi f) X + r26t8a_correctedD a beta rho Psi f X
  bound : ∀ N : ℕ, 2 ≤ N → ∀ f, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
    MemLp (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ∧
    eLpNorm (r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) +
      (∫⁻ X, ∑ i, ‖Phase2S82.configGrad (r26t8a_correctedQ a beta Psi f) X i‖ₑ ^ 2
        ∂canonicalP d N a beta) ^ (1 / 2 : ℝ) +
      eLpNorm (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ≤
        ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)))

open Classical in
def r26t8a_correctorNoise {d N : ℕ} {Omega : Type*} (a beta m b : ℝ)
    (rho : Euc d → ℝ) (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (alpha : MultiIndex d) (X : ℝ≥0 → Omega → EucConfig d N) :
    ℝ → Omega → Fin N × Fin d → ℝ :=
  fun r w i => if r ∈ Set.Icc 0 b ∧ X r.toNNReal w ∉ eucCollisionSet d N then
    Real.sqrt (2 / beta) *
      Phase2S82.configGrad (Phase2S82.pairStatistic (Psi
        (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha))))
        (X r.toNNReal w) i.1 i.2 else 0

/-- O04 in the form consumed by the observed-time packets. -/
theorem r26t8a_reversible_of_canonical (d N : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) :
    r26t8a_ReversibleWindows P X :=
  HRS.MS.S81R.s81r_canonical_reversible_windows (by omega) (by unfold criticalS; positivity) ha hbeta P hX

end HRS.MS.R26T8A

end
