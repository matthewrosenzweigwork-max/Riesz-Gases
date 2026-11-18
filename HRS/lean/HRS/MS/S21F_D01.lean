import HRS.MS.S21E_Fin
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.D01: actual particle and Gaussian realization records

Packaging of the original universal binders of the frozen statement (both records expose every realization field);
`r26t3_error` is the exactly centered error through `zetaPathW` (actual first marginal).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

structure Particle {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  X₀ : Ω → EucConfig p.d N
  W : ℝ≥0 → Ω → (Fin N → Euc p.d)
  X : ℝ≥0 → Ω → EucConfig p.d N
  brownian : IsVectorBrownian P W
  independent : IndepFun X₀ (fun ζ t => W t ζ) P
  initial : law P X₀ = r26t3_Q R N
  strong : ∀ H : ℝ, IsWholeStrongSolution P (quadraticGradientDyn p.d p.s p.a p.β) H X₀ W X

attribute [instance] Particle.mΩ Particle.prob

structure GaussianRealization {p : Parameters} {δ : ℝ} (R : Trajectory p δ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  Z : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d)
  evolution : ∀ H : ℝ, IsLinearGaussianEvolutionW P (r26t3_coeff R)
    (wholeSpaceIndex p.d) p.β⁻¹ H
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ) Z

attribute [instance] GaussianRealization.mΩ GaussianRealization.prob

def r26t3_zetapath {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (b : ℝ) : A.Ω → Window p :=
  zetaPathW (wholeSpaceIndex p.d) p.T b A.P A.X
def r26t3_Zpath {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (G : GaussianRealization R) (b : ℝ) : G.Ω → Window p :=
  processWindow (wholeSpaceIndex p.d) p.T b G.Z
def r26t3_error {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (κ : ℝ → projTensor (Window p) 3) {N : ℕ} (A : Particle R N)
    (G : GaussianRealization R) (b : ℝ) (Φ : Window p → ℝ) : ℝ :=
  |Real.sqrt N * ((∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P) -
      ∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P) -
    (1 / 6) * ∫ ζ, (κ b : TensorDual (Window p) 3)
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P|

end HRS.MS.R26T3
