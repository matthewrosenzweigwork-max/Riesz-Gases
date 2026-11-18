import Mathlib
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerC1
import HRS.MH.CoercLowerC3b

/-!
# CoercLower C3c: packet P20 (`energy_lower_pos_exists`).

Statement copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- `Cpos d s` is nonnegative for `0 < s < d`. -/
theorem clc3c_Cpos_nonneg (d : ℕ) {s : ℝ} (hs : 0 < s) (hsd : s < d) : 0 ≤ Cpos d s := by
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hds : (0 : ℝ) < (d : ℝ) - s := by linarith
  unfold Cpos
  have h1 : 0 ≤ 1 / (s * Real.Gamma (s / 2)) := one_div_nonneg.2 (mul_pos hs hG).le
  have h2 : 0 ≤ Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) :=
    mul_nonneg (div_nonneg (Real.rpow_pos_of_pos Real.pi_pos _).le hG.le)
      (div_nonneg (by norm_num) hds.le)
  linarith

/-- [P20] Lower bound of the modulated energy for `s > 0`. -/
theorem energy_lower_pos_exists (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ X : HRS.Whole.EucConfig d N, X ∉ HRS.Whole.eucCollisionSet d N →
        -(C * HRS.aNΛ d s Λ N) ≤ HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) := by
  refine ⟨Cpos d s, clc3c_Cpos_nonneg d hs hsd, ?_⟩
  intro Λ hΛ1 N hN ρ hρ hρle X hX
  have hΛ : (0 : ℝ) < Λ := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hT : (0 : ℝ) < ((N : ℝ) * Λ) ^ (2 / (d : ℝ)) :=
    Real.rpow_pos_of_pos (mul_pos hNpos hΛ) _
  have h1 := two_mul_energy_lower_pos (N := N) hd hs hsd hT hρ hρle hN X (eucCollisionSet_iff.1 hX)
  have h2 := param_pos (N := N) hd hs hsd hΛ hN
  linarith

end HRS.MH.CoercLower
