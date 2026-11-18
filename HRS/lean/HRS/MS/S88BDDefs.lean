import HRS.Whole.CriticalNoise
import HRS.MS.SuppU11
import HRS.MS.SpecAux49
import HRS.MS.MovAdjAux11
import HRS.MS.WsInitGAux5
import HRS.MS.CanThm

/-!
# S8.8 shared definitions (from the GPT-6 Pro planning skeleton `skeleton/S8.8.lean`, planning commit fa7f4ad0)

Definitions only, copied verbatim from the planning skeleton (lines 37-79) so that the S8.8 packet files
(`HRS/MS/S88BD<id>.lean`) share one owner; definitions only, no theorems.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S88Breakdown
open HRS HRS.Whole

/-- The rational-time subtype in the frozen Gaussian clause, without changing
the endpoint set or adding a continuous-version assumption. -/
abbrev S88RatTime (T : ℝ) :=
  {t : ℝ // t ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = t}

def s88Orbit {d : ℕ} (C : WholeCoeff d) (m t : ℝ) (α : MultiIndex d) : Euc d → ℝ :=
  propagatorW C 0 t (oscTestFun m α)

def s88Particle {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → EucConfig d N) (f : Euc d → ℝ) (z : Ω) : ℝ :=
  Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X z)) f - ∫ x, f x ∂(HRS.Whole.firstMarginal (law P X)))

/-- Actual chosen classical orbits: membership and compact-time bounds are
retained, so neither choice-default values nor parameterized integrals are used
without their existence/regularity hypotheses. -/
structure S88OrbitRegular {d : ℕ} (C : WholeCoeff d) (m : ℝ) : Prop where
  classical : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C t (oscTestFun m α) f
  memCb : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → MemCb 2 (s88Orbit C m t α)
  time_cont : ∀ (α : MultiIndex d) (x : Euc d) (T : ℝ), 0 ≤ T →
    ContinuousOn (fun t : ℝ => s88Orbit C m t α x) (Set.Icc (0 : ℝ) T)
  local_bdd : ∀ (α : MultiIndex d) (T : ℝ), 0 ≤ T →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      |s88Orbit C m t α x| ≤ B

/-- Only the two actual L2 estimates needed by initial decay. Increments are
centered before the variance/covariance input is applied. -/
structure S88OrbitEnvelope {d : ℕ} (C : WholeCoeff d) (μ : Measure (Euc d))
    (m c : ℝ) (b : MultiIndex d → ℝ) : Prop where
  base : ∀ (α : MultiIndex d) (u : ℝ), 1 ≤ u →
    MemLp (HRS.Whole.projMean μ (s88Orbit C m u α)) 2 μ ∧
      (∫ x, HRS.Whole.projMean μ (s88Orbit C m u α) x ^ 2 ∂μ) ≤
        b α * Real.exp (-2 * c * u)
  increment : ∀ (α : MultiIndex d) (u s t : ℝ), 1 ≤ u → 0 ≤ s → 0 ≤ t →
    MemLp (HRS.Whole.projMean μ (fun x => s88Orbit C m (u + s) α x - s88Orbit C m (u + t) α x)) 2 μ ∧
      (∫ x, HRS.Whole.projMean μ (fun y => s88Orbit C m (u + s) α y -
          s88Orbit C m (u + t) α y) x ^ 2 ∂μ) ≤
        b α * Real.exp (-2 * c * u) * (s - t) ^ 2

def s88Constant {d : ℕ} (T Cin : ℝ) (b : MultiIndex d → ℝ) : ℝ :=
  Real.sqrt (64 * max Cin 1 * (1 + T ^ 2) * ∑' α, b α)

/-! ## A01: actual classical orbits, including every m above the frozen index -/


end HRS.MS.S88Breakdown
