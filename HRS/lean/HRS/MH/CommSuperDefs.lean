import HRS.Whole.AppendixBEnergy
import HRS.Energy.Commutator.SuperAssembly
import HRS.Commutator.Whole.Bridge

/-!
# Definitions shared by the packets of `whole_commutator_super` (S.B.5(i)); see `CommSuperSpec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- The torus density of the dilated data: `ρ_t(z) = t^{-d} ρ(t⁻¹ · centeredRep z)`. -/
def concDens (t : ℝ) (ρ : Euc d → ℝ) (z : Torus d) : ℝ :=
  (t ^ d)⁻¹ * ρ (t⁻¹ • KernelGrad.centeredRep z)

/-- The embedding `x ↦ mk (t x)` of `ℝ^d` into the torus (injective on `‖x‖ ≤ 1/(16 t)`). -/
def concMap (t : ℝ) (x : Euc d) : Torus d := Torus.mk (t • x)

/-- The estimate for bounded densities with compact support (radius `R0`), no log moment. -/
def CompactCase (d : ℕ) (s C₀ C : ℝ) : Prop :=
  0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ →
    (∀ x, ρ x ≤ Λ) → ∀ R0 : ℝ, (∀ x, R0 < ‖x‖ → ρ x = 0) →
    ∀ X : Whole.EucConfig d N, Function.Injective X → (∀ i, ‖X i‖ ≤ R0) →
    ∀ (v : Euc d → Euc d) (K : ℝ), Whole.HasLipBoundW v K →
      |Whole.commN d s v X (Whole.withDensityReal ρ)| ≤
        C * K * (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N)

end HRS.MH.CommSuper
