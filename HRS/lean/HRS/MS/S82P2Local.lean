import HRS.MS.S82P2Defs
import HRS.MS.FeatDecAux3

/-!
# S8.2 weighted two-particle corrector: definitions (port of the fixed skeleton Local file)
Only definitions and the proved pointwise uniqueness lemma; the producer theorems are not ported.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- Native pointwise uniqueness fixes the apparent `exists C, forall rho`
quantifier change in P06/P07. No uniformity in rho is inferred from hS8C. -/
theorem critical_thermal_eq (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    rho = HRS.Whole.thermalDensity d (criticalS d) a beta := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  exact (HRS.MS.S85.s85_thermal_eq hd
    (by dsimp [criticalS]; positivity)
    (by dsimp [criticalS]; linarith) ha hbeta hrho).1

def NewtonCutoff {d : ℕ} (chi : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ chi ∧ (∀ z, chi (-z) = chi z) ∧
    (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
    (∀ z, ‖z‖ ≤ 1 → chi z = 1) ∧ (∀ z, 2 ≤ ‖z‖ → chi z = 0)

def newtonKernel (d : ℕ) (nu : ℝ) (z : Euc d) : ℝ :=
  if d = 2 then -(Real.log ‖z‖) / (2 * nu * sphereArea d)
  else ‖z‖ ^ (2 - (d : ℝ)) / (2 * nu * ((d : ℝ) - 2) * sphereArea d)

def rawNewton {d : ℕ} (nu : ℝ) (chi : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  chi (x - y) * ∫ z, newtonKernel d nu (x - y - z) * chi z *
    midPair F ((1 / 2 : ℝ) • (x + y)) z

def localNewton {d : ℕ} (mu : Measure (Euc d)) (nu : ℝ) (chi : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) : Euc d → Euc d → ℝ :=
  r2CenterKernel mu (rawNewton nu chi F)

def newtonDefect {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  F x y + pairA C mu (localNewton mu C.ν chi F) x y

-- BEGIN S82.P01

/-- Native weighted corrector. Every polynomial and constant is chosen before f.
All row integrability and diagonal regularity requirements are explicit. -/
structure PairCorrector {d : ℕ} (a beta : ℝ) (rho : Euc d → ℝ)
    (M A : ℝ) (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) : Prop where
  measurable : Measurable (Function.uncurry Q)
  smooth : ContDiffOn ℝ 8 (Function.uncurry Q) {p | p.1 ≠ p.2}
  symmetric : ∀ x y, Q x y = Q y x
  canonical : CanonicalPair (HRS.Whole.withDensityReal rho) Q
  poisson : ∀ x y, x ≠ y →
    -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
      HSource (HRS.Whole.withDensityReal rho) f x y
  value : ∀ x y, x ≠ y →
    |Q x y| ≤ A * pairWeight M x y *
      (1 + smallRadius x y ^ (2 - criticalS d) +
        if d = 4 then |Real.log (smallRadius x y)| else 0)
  gradient : ∀ x y, x ≠ y →
    ‖pairGradX Q x y‖ + ‖pairGradY Q x y‖ ≤
      A * pairWeight M x y * (1 + smallRadius x y ^ (1 - criticalS d))
  hessian : ∀ x y, x ≠ y →
    ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (x, y)‖ ≤
      A * pairWeight M x y * (1 + smallRadius x y ^ (-criticalS d))
  tangential : Conormal 6 1 M (criticalS d - 2) A Q
  nonlocal : CanonicalPair (HRS.Whole.withDensityReal rho)
      (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) ∧
    ∀ x y, x ≠ y →
      |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y| ≤
        A * pairWeight M x y * (1 + smallRadius x y ^ (-criticalS d))

end HRS.MS.Phase2S82
