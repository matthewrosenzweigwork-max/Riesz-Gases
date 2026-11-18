import HRS.MS.LogBndAux1

/-!
# C-LB: proof of `HRS.Whole.logThermal_bounds`

For `s = 0`, `thermalDensity d 0 a β = thermalRep K̃ γ̄ β μ` pointwise (`clb_thermalDensity_eq_rep`), an everywhere Euler
fixed point in `C_M` for `K̃ = g + ½ l(x) + ½ l(y) + ½ log 2`, `γ̄ = (1+|x|²)^{β/2} e^{-βa|x|²/2} / c̄`
(`c̄ = t67cbar d a β`).  Since `0 ≤ K̃ * ρ ≤ M B` (K1 for `K̃`; the `x`-dependent terms of `K̃` are what produce the
factor `(1+|x|²)^{β/2}` inside `γ̄`), `clb_rep_bounds` gives `e^{-β M B} γ̄ ≤ ρ ≤ e^{β B} γ̄`, i.e. the claim with
`c = e^{-β M B} / c̄` and `C = e^{β B} / c̄`.  No statement was adjusted.

Exports: `logThermal_bounds_proof : type_of% @HRS.Whole.logThermal_bounds`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- Closed form of the reference density `γ̄`. -/
lemma clb_gammaBar_eq {a β : ℝ} (x : Euc d) :
    t67gammaBar d a β x =
      (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) / t67cbar d a β := by
  unfold t67gammaBar t67w t67l confinement
  congr 1
  have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hpos, ← Real.exp_add]
  congr 1
  ring

/-- **C-LB.**  The two-sided bound for the logarithmic thermal density. -/
theorem logThermal_bounds_proof : type_of% @HRS.Whole.logThermal_bounds := by
  intro d hd a β ha hβ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, M, μ, hS, hM, hρC, hρfix, hpt⟩ := clb_thermalDensity_eq_rep hd1 ha hβ
  have hcb := t67cbar_pos (d := d) ha hβ
  refine ⟨Real.exp (-β * (M * B)) / t67cbar d a β, div_pos (Real.exp_pos _) hcb,
    Real.exp (β * B) / t67cbar d a β, fun x => ?_⟩
  obtain ⟨hlo, hhi⟩ := clb_rep_bounds hS hβ.le (by linarith) hρC hρfix x
  rw [hpt x]
  rw [clb_gammaBar_eq] at hlo hhi
  constructor
  · calc Real.exp (-β * (M * B)) / t67cbar d a β * (1 + ‖x‖ ^ 2) ^ (β / 2) *
          Real.exp (-β * a * ‖x‖ ^ 2 / 2)
        = Real.exp (-β * (M * B)) *
          ((1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) / t67cbar d a β) := by ring
      _ ≤ _ := hlo
  · calc _ ≤ Real.exp (β * B) *
          ((1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) / t67cbar d a β) := hhi
      _ = _ := by ring

end HRS.MS.Thm

end
