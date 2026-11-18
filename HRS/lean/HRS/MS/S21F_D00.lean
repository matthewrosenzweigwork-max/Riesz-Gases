import HRS.Whole.Round2

/-!
# S21F, packet R26-T3.D00: physical parameters and exact resulting-trajectory data

Transparent records and abbreviations for the S2.1(iii) entry packets (no analytic assumption is bundled).
Constants in `Parameters` are chosen before the trajectory; `c₁`, `C₁` are unrestricted (a nonempty
`Trajectory` forces `0 < c₁` through `IsResultingSolution.cpos`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

/-- Constants in Parameters are chosen before the trajectory. This record adds no hypothesis to the frozen endpoint. -/
structure Parameters where
  d : ℕ
  hd : 2 ≤ d
  s : ℝ
  hs0 : 0 ≤ s
  hs : s < (d : ℝ) / 2
  a : ℝ
  ha : 0 < a
  β : ℝ
  hβ : 0 < β
  γ : ℝ
  hγ : 0 ≤ γ
  hγs : 0 < s → 0 < γ
  T : ℝ
  hT : 0 < T
  c₁ : ℝ
  C₁ : ℝ

/-- The exact frozen datum after a common radius has been selected. -/
structure Trajectory (p : Parameters) (δ : ℝ) where
  ρβ : Euc p.d → ℝ
  thermal : IsThermalEquilibrium p.d p.s p.a p.β ρβ
  ε : ℝ
  ψ : Euc p.d → ℝ
  admissible : IsAdmissiblePerturbation ρβ δ ε ψ
  ρ : ℝ → Euc p.d → ℝ
  resulting : IsResultingSolution p.d p.s p.a p.β ρβ δ ε ψ p.c₁ p.C₁ ρ

def r26t3_mu {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (t : ℝ) : Measure (Euc p.d) :=
  HRS.Whole.withDensityReal (R.ρ t)
def r26t3_coeff {p : Parameters} {δ : ℝ} (R : Trajectory p δ) : WholeCoeff p.d :=
  (quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ
abbrev Window (p : Parameters) := OscPath p.d (wholeSpaceIndex p.d) p.T
def r26t3_U {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (u t : ℝ) (f : Euc p.d → ℝ) : Euc p.d → ℝ :=
  propagatorW (r26t3_coeff R) u t f
def r26t3_Q {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ) : Measure (EucConfig p.d N) :=
  HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.γ (r26t3_mu R 0)
def r26t3_a {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (f : Euc p.d → ℝ) : Euc p.d → ℝ :=
  HRS.Whole.responseRepW (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f

end HRS.MS.R26T3
