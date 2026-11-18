import HRS.PDE.Hadamard
import HRS.PDE.MeanFieldDefs
import HRS.Main.Headline

/-!
# EdgeSharp: definitions shared by the packets of `edgeworth_sharpness_homogeneous`

No `sorry` here.  See `HRS/MH/EdgeSharpPlan.md`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

/-- The observation `φ₀ = ψ_k + b ψ_{2k}` (`ψ_k = √2 cos(2πk·x)`). -/
def phi0 (k : Lattice d) (b : ℝ) : Torus d → ℝ :=
  fun x => PDE.cosTest k x + b * PDE.cosTest ((2 : ℤ) • k) x

/-- The cross-covariance density `χ^r = e^{rA}(R φ₀)` on the homogeneous torus:
`R φ₀ = (1+βĝ(k))⁻¹ ψ_k + b (1+βĝ(2k))⁻¹ ψ_{2k}` (`q42_responseInverse_eq`) evolved by the forward semigroup, which is
diagonal on cosines with eigenvalue `modelEigenvalue d s β⁻¹ (-1) k = -(2π|k|)²(β⁻¹+ĝ(k))`. -/
def crossDensity (d : ℕ) (s β : ℝ) (k : Lattice d) (b r : ℝ) : Torus d → ℝ := fun x =>
  (1 + β * rieszCoeff d s k)⁻¹ * Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * r) * PDE.cosTest k x +
  b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹ *
    Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) ((2 : ℤ) • k) * r) * PDE.cosTest ((2 : ℤ) • k) x

end HRS.MH.EdgeSharp
