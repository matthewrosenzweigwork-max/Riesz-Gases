import Mathlib
import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerC3c
import HRS.MH.CoercLowerD4d

/-!
# CoercLower final: packet P32 (`completionNonnegRd_exists`).

Statement copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- [P32] The goal, exactly as in the plan. -/
theorem completionNonnegRd_exists (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ C₀ : ℝ, C₀' ≤ C₀ → HRS.Whole.AppendixA.CompletionNonnegRd d s C₀ := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨C, hC0, hC⟩ := energy_lower_log_exists (d := d) hd
    refine ⟨C, hC0, fun C₀ hC₀ => ⟨hC0.trans hC₀, ?_⟩⟩
    intro Λ hΛ N hN ρ hρ hρΛ hint X hX
    have hN1 : 1 ≤ N := by omega
    have h := hC Λ hΛ N hN1 ρ hρ hρΛ (hint rfl) X hX
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hdiv : C / N ≤ C₀ / N := div_le_div_of_nonneg_right hC₀ hNpos.le
    have ho : HRS.oNΛ d 0 C₀ Λ N = Real.log ((N : ℝ) * Λ) / (2 * d * N) + C₀ / N := by
      simp [HRS.oNΛ, Real.rpow_neg_one, div_eq_mul_inv]
    rw [ho]
    linarith
  · obtain ⟨C, hC0, hC⟩ := energy_lower_pos_exists (d := d) hd hpos hsd
    refine ⟨C, hC0, fun C₀ hC₀ => ⟨hC0.trans hC₀, ?_⟩⟩
    intro Λ hΛ N hN ρ hρ hρΛ _ X hX
    have hN1 : 1 ≤ N := by omega
    have h := hC Λ hΛ N hN1 ρ hρ hρΛ X hX
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have ha : 0 < HRS.aNΛ d s Λ N :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hNpos _)
    have ho : HRS.oNΛ d s C₀ Λ N = C₀ * HRS.aNΛ d s Λ N := by
      simp [HRS.oNΛ, HRS.aNΛ, hpos.ne', mul_assoc]
    rw [ho]
    nlinarith [mul_le_mul_of_nonneg_right hC₀ ha.le]

end HRS.MH.CoercLower
