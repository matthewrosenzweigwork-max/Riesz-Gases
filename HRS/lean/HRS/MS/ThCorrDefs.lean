import HRS.Whole.Thermal
import HRS.MS.GapRefAux1

/-!
# S4.4 thermal-corrector chain: interface structures (statements only, no theorems)

`TcRef d s ρ M₀ c S N`: the data of the thermal density `ρ` that the response, far-convolution, Sobolev-iteration and
smoothing packets (TC-2, TC-4, TC-5, TC-S) consume.  All of them are stated for an arbitrary `ρ` with `TcRef`
and constants quantified BEFORE `ρ`; the packet TC-U proves that the thermal densities for `(a, β)` in compact sets satisfy
`TcRef` with uniform constants (see `docs/TC_PLAN.md` section 2).
-/

open MeasureTheory
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.TcDefs

open HRS.Whole

variable {d : ℕ}

/-- Interface of a thermal density `ρ`: a smooth, positive probability density with a Gaussian upper bound and
Gaussian-weighted derivative bounds up to order `N`. -/
structure TcRef (d : ℕ) (ρ : Euc d → ℝ) (M₀ c S : ℝ) (N : ℕ) : Prop where
  prob : HRS.Whole.IsProbDensity ρ
  pos : ∀ x, 0 < ρ x
  smooth : ContDiff ℝ ∞ ρ
  gauss : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)
  deriv : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)

/-- Drift data of the thermal density: `∇ρ = ρ (−q x + B)`, `B ∈ C_b^m` with bound `Mb`, second moment `≤ m₂`
(the Poisson step of S4.4 uses `GapRef`, `HRS/MS/GapRefAux1.lean`; this structure records the uniform constants). -/
structure TcDrift (d : ℕ) (ρ : Euc d → ℝ) (q Mb m₂ : ℝ) (m : ℕ) : Prop where
  gap : ∃ B : Euc d → Euc d, HRS.MS.Gap.GapRef d ρ q B ∧ HRS.Whole.HasCbBound m Mb B
  moment : ∫ x, ‖x‖ ^ 2 * ρ x ≤ m₂

end HRS.MS.TcDefs

end
