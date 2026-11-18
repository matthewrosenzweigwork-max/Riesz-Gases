import HRS.Whole.CriticalNoise
import HRS.Whole.Round2
import HRS.Equilibrium.Q84eAuxI

/-!
# S8.2 native definitions for the critical normal form
Definitions only (port of the fixed skeleton Defs).
The Riesz normalization is literal |x|^(-s), without a 1/s factor.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

def criticalS (d : ℕ) : ℝ := (d : ℝ) / 2
def testOrder (d : ℕ) : ℕ := 8 * d + 80
def iterationCount (d : ℕ) : ℕ := 2 * d + 24

def TestBound {d : ℕ} (k : ℕ) (A : ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A

def testSizeE {d : ℕ} (k : ℕ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ j : Fin k, ⨆ x, ENNReal.ofReal ‖iteratedFDeriv ℝ ((j : ℕ) + 1) f x‖

def pairWeight {d : ℕ} (M : ℝ) (x y : Euc d) : ℝ :=
  jbracket x ^ M * jbracket y ^ M

def smallRadius {d : ℕ} (x y : Euc d) : ℝ := min 1 ‖x - y‖

def midPair {d : ℕ} (F : Euc d → Euc d → ℝ) (X z : Euc d) : ℝ :=
  F (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)

def mixedJet {d : ℕ} (p q : ℕ) (F : Euc d → Euc d → ℝ) (X z : Euc d) :=
  iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (midPair F Y) z) X

/-- Control all mixed center/relative derivatives, not merely radial size. -/
def Conormal {d : ℕ} (k b : ℕ) (M sigma A : ℝ)
    (F : Euc d → Euc d → ℝ) : Prop :=
  ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2} ∧
  ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d, z ≠ 0 →
    ‖mixedJet p q F X z‖ ≤
      A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + (min 1 ‖z‖) ^ (-(sigma + q)) *
          (1 + |Real.log (min 1 ‖z‖)|) ^ b)

def CanonicalPair {d : ℕ} (mu : Measure (Euc d))
    (F : Euc d → Euc d → ℝ) : Prop :=
  (∀ y, Integrable (fun x => F x y) mu) ∧
  (∀ x, Integrable (F x) mu) ∧ HRS.Whole.IsDoublyCentered mu F

def hSource {d : ℕ} (f : Euc d → ℝ) : Euc d → Euc d → ℝ :=
  commutatorKernel d (criticalS d) (gradient f)

def HSource {d : ℕ} (mu : Measure (Euc d)) (f : Euc d → ℝ) : Euc d → Euc d → ℝ :=
  fun x y => (1 / 2) * r2CenterKernel mu (hSource f) x y

def aSource {d : ℕ} (mu : Measure (Euc d)) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  (1 / 2) * ∫ y, hSource f x y ∂mu

def pairA {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  HRS.Whole.projGeneratorW C mu 0 (fun x' => F x' y) x +
    HRS.Whole.projGeneratorW C mu 0 (F x) y

def oneJ {d : ℕ} (C : WholeCoeff d) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  generatorW C 0 f x - C.ν * Laplacian.laplacian f x -
    inner ℝ (C.drift 0 x) (gradient f x)

def pairJ {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  HRS.Whole.projMean mu (fun x' => oneJ C (fun w => F w y) x') x +
    HRS.Whole.projMean mu (fun y' => oneJ C (F x) y') y

def forceMean {d : ℕ} (rho : Euc d → ℝ) : Euc d → Euc d :=
  convGradConvW (rieszKernelGrad d (criticalS d)) rho

def centeredForce {d : ℕ} (rho : Euc d → ℝ) (x z : Euc d) : Euc d :=
  rieszKernelGrad d (criticalS d) (x - z) - forceMean rho x

def pairGradX {d : ℕ} (F : Euc d → Euc d → ℝ) (x y : Euc d) : Euc d :=
  gradient (fun x' => F x' y) x

def pairGradY {d : ℕ} (F : Euc d → Euc d → ℝ) (x y : Euc d) : Euc d :=
  gradient (F x) y

def tripleT {d : ℕ} (rho : Euc d → ℝ) (F : Euc d → Euc d → ℝ)
    (x y z : Euc d) : ℝ :=
  -inner ℝ (centeredForce rho x z) (pairGradX F x y) -
    inner ℝ (centeredForce rho y z) (pairGradY F x y)

def tripleG {d : ℕ} (C : WholeCoeff d) (rho : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) (x y z : Euc d) : ℝ :=
  (tripleT rho F x y z + tripleT rho F x z y + tripleT rho F y z x -
    pairJ C (HRS.Whole.withDensityReal rho) F x y -
    pairJ C (HRS.Whole.withDensityReal rho) F x z -
    pairJ C (HRS.Whole.withDensityReal rho) F y z) / 3

def repeatedB {d : ℕ} (rho : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  inner ℝ (rieszKernelGrad d (criticalS d) (x - y))
    (pairGradX F x y - pairGradY F x y) -
  2 * (inner ℝ (forceMean rho x) (pairGradX F x y) +
    inner ℝ (forceMean rho y) (pairGradY F x y))

def pairSum {d N : ℕ} (F : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, F (X i) (X j)

def tripleSum {d N : ℕ} (G : Euc d → Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
    G (X i) (X j) (X k)

def pairStatistic {d N : ℕ} (F : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSum F X

def errorStatistic {d N : ℕ} (C : WholeCoeff d) (rho : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  -(2 / (N : ℝ)) * pairStatistic (pairJ C (HRS.Whole.withDensityReal rho) F) X +
    (N : ℝ) ^ (-(5 / 2 : ℝ)) *
      (tripleSum (tripleG C rho F) X - pairSum (repeatedB rho F) X)

def centerUnder {E : Type*} [MeasurableSpace E] (P : Measure E) (f : E → ℝ) (x : E) : ℝ :=
  f x - ∫ y, f y ∂P

def configGrad {d N : ℕ} (F : EucConfig d N → ℝ) (X : EucConfig d N) (i : Fin N) : Euc d :=
  gradient (fun y => F (Function.update X i y)) (X i)

def particleGenerator {d N : ℕ} (D : WholeDyn d) (F : EucConfig d N → ℝ)
    (X : EucConfig d N) : ℝ :=
  D.invβ * ∑ i, Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) +
    ∑ i, inner ℝ (particleDriftW D X i) (configGrad F X i)

def canonicalP (d N : ℕ) (a beta : ℝ) : Measure (EucConfig d N) :=
  HRS.Whole.canonicalGibbs (rieszKernel d (criticalS d)) (confinement a) N beta

def scalarForcing {d N : ℕ} (a beta : ℝ) (rho : Euc d → ℝ)
    (f : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (Real.sqrt N / 2) * centerUnder (canonicalP d N a beta)
    (fun Y => centeredPairFunctional (hSource f) Y (HRS.Whole.withDensityReal rho)) X

/-- Fixed-N closure in both the generator graph norm and Dirichlet norm.
The approximants avoid collisions and have compact spatial support. -/
def GeneratorClosure {d N : ℕ} (a beta : ℝ) (F LF : EucConfig d N → ℝ) : Prop :=
  MemLp F 2 (canonicalP d N a beta) ∧
  MemLp LF 2 (canonicalP d N a beta) ∧
  (∀ i, MemLp (fun X => configGrad F X i) 2 (canonicalP d N a beta)) ∧
  ∃ Fn : ℕ → EucConfig d N → ℝ,
    (∀ n, ContDiff ℝ ∞ (Fn n) ∧ HasCompactSupport (Fn n) ∧
      tsupport (Fn n) ⊆ (eucCollisionSet d N)ᶜ) ∧
    HRS.TendstoL2 (canonicalP d N a beta) Fn F ∧
    HRS.TendstoL2 (canonicalP d N a beta)
      (fun n => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n)) LF ∧
    ∀ i, Tendsto (fun n => eLpNorm (fun X =>
      configGrad (Fn n) X i - configGrad F X i) 2 (canonicalP d N a beta)) atTop (𝓝 0)

end HRS.MS.Phase2S82

