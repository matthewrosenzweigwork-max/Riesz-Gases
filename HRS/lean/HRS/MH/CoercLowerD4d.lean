import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerD4a
import HRS.MH.CoercLowerD4c
import Mathlib

/-!
# CoercLower packet P31 (`energy_lower_log_exists`): lower bound of the modulated energy for `s = 0`.

Combines `two_mul_energy_lower_log` (P29) with the parameter choice `param_log` (P30), then divides by 2.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- [P31] Lower bound of the modulated energy for `s = 0`. -/
theorem energy_lower_log_exists (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) →
      Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ) →
      ∀ X : HRS.Whole.EucConfig d N, X ∉ HRS.Whole.eucCollisionSet d N →
        -(Real.log ((N : ℝ) * Λ) / (2 * d * N) + C / N) ≤
          HRS.Whole.rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := param_log (d := d) hd
  refine ⟨C, hC0, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ hlog X hXc
  have hX : Function.Injective X := eucCollisionSet_iff.mp hXc
  obtain ⟨hT, hineq⟩ := hC Λ hΛ N hN
  have h29 := two_mul_energy_lower_log hd hT hρ hΛρ hlog hN X hX
  linarith

end HRS.MH.CoercLower
