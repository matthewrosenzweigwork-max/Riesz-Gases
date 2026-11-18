import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercTestW6
import HRS.MH.CoercLowerC1
import HRS.MH.CoercLowerD4a

/-!
# `qform_gTs_le_energy` (packet W7c): `Qform gT ≤ 2 (F_N + 𝔬_N)` at `T = (NΛ)^{2/d}`.

Statement copied verbatim from `HRS/MH/CoercTestSpec.lean`; the proof uses `qform_gT_le_pos` (W6a),
`qform_gT_le_log` (W6b), `param_pos` (CoercLowerC1) and `param_log` (CoercLowerD4a).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- [W7c] With `T = (NΛ)^{2/d}`: `Qform gT ≤ 2 (F_N + 𝔬_N)` for `C₀ ≥ C₀'`.  Route: W6a/W6b, then the proved
parameter identities `param_pos` (C1:149), `param_log` (D4a:18) and `oNΛ = C₀ aNΛ` resp.
`log(NΛ)/(2dN) + C₀/N` as in `completionNonnegRd_exists` (CoercLowerFinal:23). -/
theorem qform_gTs_le_energy (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ C₀ : ℝ, C₀' ≤ C₀ → ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) →
      ∀ X : HRS.Whole.EucConfig d N, Function.Injective X →
        Qform (gTs d s (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) X ρ ≤
          2 * (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀ Λ N) := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨C, hC0, hC⟩ := param_log (d := d) hd
    refine ⟨max 0 C, le_max_left _ _, fun C₀ hC₀ => ?_⟩
    intro Λ hΛ N hN ρ hρ hρΛ hint X hX
    have hN1 : 1 ≤ N := hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hCC : C ≤ C₀ := (le_max_right _ _).trans hC₀
    have hdiv : C / N ≤ C₀ / N := div_le_div_of_nonneg_right hCC hNpos.le
    have hg : ∀ T : ℝ, gTs d 0 T = HRS.MH.CoercLower.gTlog T := fun T => by simp [gTs]
    have h := hC Λ hΛ N hN1
    have hq := qform_gT_le_log (d := d) (N := N) hd h.1 hρ hρΛ (hint rfl) hN1 X hX
    have ho : HRS.oNΛ d 0 C₀ Λ N = Real.log ((N : ℝ) * Λ) / (2 * d * N) + C₀ / N := by
      simp [HRS.oNΛ, Real.rpow_neg_one, div_eq_mul_inv]
    rw [hg, ho]
    linarith [hq, h.2, hdiv]
  · have hsne : s ≠ 0 := hpos.ne'
    have hg : ∀ T : ℝ, gTs d s T = HRS.MH.CoercLower.gTpos s T := fun T => by simp [gTs, hsne]
    refine ⟨max 0 (Cpos d s), le_max_left _ _, fun C₀ hC₀ => ?_⟩
    have hCC : Cpos d s ≤ C₀ := (le_max_right _ _).trans hC₀
    intro Λ hΛ N hN ρ hρ hρΛ _ X hX
    have hΛ0 : (0 : ℝ) < Λ := by linarith
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hT0 : (0 : ℝ) < ((N : ℝ) * Λ) ^ (2 / (d : ℝ)) :=
      Real.rpow_pos_of_pos (mul_pos hNpos hΛ0) _
    have hq := qform_gT_le_pos (d := d) (N := N) hd hpos hsd hT0 hρ hρΛ hN X hX
    have hp := param_pos (d := d) (N := N) hd hpos hsd hΛ0 hN
    have ha : 0 ≤ HRS.aNΛ d s Λ N :=
      mul_nonneg (Real.rpow_nonneg hΛ0.le _) (Real.rpow_nonneg hNpos.le _)
    have ho : HRS.oNΛ d s C₀ Λ N = C₀ * HRS.aNΛ d s Λ N := by
      simp [HRS.oNΛ, HRS.aNΛ, hsne, mul_assoc]
    have hmul : Cpos d s * HRS.aNΛ d s Λ N ≤ C₀ * HRS.aNΛ d s Λ N :=
      mul_le_mul_of_nonneg_right hCC ha
    rw [hg, ho]
    linarith [hq, hp, hmul]

end HRS.MH.CoercTest
