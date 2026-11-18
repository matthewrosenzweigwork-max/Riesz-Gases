import HRS.MS.SA16ZL3

/-!
# S.A.16 (SA16Z) L4: the near part estimate `∫⁻ (∫⁻ κ D)^p ≤ (∫⁻ κ)^p ∫⁻ ‖Df‖^p`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L4
variable {d : ℕ}

theorem sa16z_near_Lp {f : Euc d → ℝ} (hf : IsCcInfty f) {κ : Euc d → ℝ≥0∞} (hκ : Measurable κ)
    (hA : ∫⁻ z, κ z ≠ ⊤) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, (∫⁻ z, κ z * sa16z_D f x z) ^ p ≤ (∫⁻ z, κ z) ^ p * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hAp : (∫⁻ z, κ z) ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hA
  have h1 : ∫⁻ x, (∫⁻ z, κ z * sa16z_D f x z) ^ p ≤
      ∫⁻ x, (∫⁻ z, κ z) ^ (p - 1) * ∫⁻ z, κ z * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p :=
    lintegral_mono fun x => sa16z_step1 hf hκ hA hp x
  rw [lintegral_const_mul' _ _ hAp, sa16z_swap_kappa hf hκ, ← mul_assoc] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  by_cases hA0 : ∫⁻ z, κ z = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp0, ENNReal.zero_rpow_of_pos (by linarith)]; simp
  · conv_rhs => rw [show p = (p - 1) + 1 by ring]
    rw [ENNReal.rpow_add _ _ hA0 hA, ENNReal.rpow_one]

end L4

end HRS.Whole.AppendixA.Phase2SA16R
