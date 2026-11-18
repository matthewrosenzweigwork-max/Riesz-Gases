import HRS.MS.SA16ZD5
import HRS.MS.S16FracAux1

/-!
# S.A.16 (SA16Z) E1: Glaeser normalisation `∂_aμ = √μ ĥ_a` and the coefficient matrix of the absorbed terms
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E1
variable {d : ℕ}

/-- `ĥ_a = ∂_aμ / √μ` (`0` where `μ = 0`) -/
def sa16z_hh (μ : Euc d → ℝ) (a : Fin d) (x : Euc d) : ℝ :=
  if μ x = 0 then 0 else sa16z_dm μ a x / Real.sqrt (μ x)

lemma sa16z_glaeser {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hpos : ∀ x, 0 ≤ μ x) {Λ : ℝ}
    (hCb : sa16z_Cb 2 Λ μ) (a : Fin d) (x : Euc d) :
    sa16z_dm μ a x ^ 2 ≤ 2 * Λ * μ x := by
  have h := HRS.S16Frac.s16frac_glaeser (hμ.of_le (by simp)) hpos (M := Λ) (fun y => hCb 2 le_rfl y) x
  have h2 : |sa16z_dm μ a x| ≤ ‖fderiv ℝ μ x‖ := by
    have := (fderiv ℝ μ x).le_opNorm (sa16z_e a)
    simpa [sa16z_dm, sa16z_e, Real.norm_eq_abs] using this
  calc sa16z_dm μ a x ^ 2 = |sa16z_dm μ a x| ^ 2 := (sq_abs _).symm
    _ ≤ ‖fderiv ℝ μ x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ ≤ _ := h

lemma sa16z_hh_mul {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hpos : ∀ x, 0 ≤ μ x) {Λ : ℝ}
    (hCb : sa16z_Cb 2 Λ μ) (a : Fin d) (x : Euc d) :
    sa16z_dm μ a x = Real.sqrt (μ x) * sa16z_hh μ a x := by
  unfold sa16z_hh
  split_ifs with h
  · have := sa16z_glaeser hμ hpos hCb a x
    rw [h, mul_zero] at this
    have : sa16z_dm μ a x ^ 2 ≤ 0 := by simpa using this
    simpa using pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
  · have hp : 0 < Real.sqrt (μ x) := Real.sqrt_pos.2 (lt_of_le_of_ne (hpos x) (Ne.symm h))
    field_simp

lemma sa16z_hh_abs {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hpos : ∀ x, 0 ≤ μ x) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb 2 Λ μ) (a : Fin d) (x : Euc d) : |sa16z_hh μ a x| ≤ Real.sqrt (2 * Λ) := by
  unfold sa16z_hh
  split_ifs with h
  · simp
  · have hp : 0 < Real.sqrt (μ x) := Real.sqrt_pos.2 (lt_of_le_of_ne (hpos x) (Ne.symm h))
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have := sa16z_glaeser hμ hpos hCb a x
    have h1 : |sa16z_dm μ a x| ≤ Real.sqrt (2 * Λ * μ x) := Real.abs_le_sqrt this
    calc |sa16z_dm μ a x| ≤ Real.sqrt (2 * Λ * μ x) := h1
      _ = Real.sqrt (2 * Λ) * Real.sqrt (μ x) := Real.sqrt_mul (by linarith) _

end E1

end HRS.Whole.AppendixA.Phase2SA16R
