import HRS.Whole.AppendixBKernel

/-!
# Definitions shared by the packets of `B:lem:screened` (S.B.4); see `ScreenedPlan.md`, `ScreenedSpec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Explicit cell coefficients `K_{zz'} = c₁ 1_{|z-z'| ≤ R} + c₂ ω_{z'}` (nonnegative parameters). -/
def kcCoef (d : ℕ) (R c₁ c₂ : ℝ) (z z' : Fin d → ℤ) : ℝ≥0 :=
  Real.toNNReal (c₁ * (if ‖latticePt z - latticePt z'‖ ≤ R then 1 else 0) + c₂ * cellWeight d z')

/-- Gagliardo double integral `∬ |u(x+h)-u(x)|² |h|^{-d-2σ} dx dh` in `ℝ≥0∞`. -/
def gagSq (σ : ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * ∫⁻ x : Euc d, ‖u (x + h) - u x‖ₑ ^ 2

end HRS.MH.Screened
