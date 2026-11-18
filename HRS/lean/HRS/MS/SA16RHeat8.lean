import HRS.MS.SA16RHeat7

/-!
# S.A.16 (SA16R) Heat8: the heat kernel is an approximate identity in `L^p`

`sa16r_g_tail`: `∫_{‖z‖ ≥ δ} g_a ≤ 2^{d/2} exp(-δ²/(8a))`.
`sa16r_approx_id`: for `u` continuous with compact support, `‖g_a ⋆ u - u‖_p → 0` as `a → 0+`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat8
variable {d : ℕ}

lemma sa16r_g_tail_pointwise {a : ℝ} (ha : 0 < a) {δ : ℝ} (z : Euc d) (hz : δ ≤ ‖z‖) (hδ : 0 ≤ δ) :
    sa16r_g d a z ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a))) * sa16r_g d (2 * a) z := by
  have h2a : 0 < 2 * a := by positivity
  have hN : 0 < 4 * Real.pi * a := by positivity
  have hpre : (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * a)) ^ (-((d : ℝ) / 2)) := by
    have h4 : 4 * Real.pi * (2 * a) = 2 * (4 * Real.pi * a) := by ring
    rw [h4, Real.mul_rpow (by norm_num) hN.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hexp : Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2) ≤
      Real.exp (-(δ ^ 2 / (8 * a))) * Real.exp (-(1 / (4 * (2 * a))) * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : δ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hδ hz 2
    have : -(1 / (4 * a)) * ‖z‖ ^ 2 = -(‖z‖ ^ 2 / (8 * a)) + (-(‖z‖ ^ 2 / (8 * a))) := by field_simp; ring
    have h2 : -(1 / (4 * (2 * a))) * ‖z‖ ^ 2 = -(‖z‖ ^ 2 / (8 * a)) := by field_simp; ring
    rw [this, h2]
    have : -(‖z‖ ^ 2 / (8 * a)) ≤ -(δ ^ 2 / (8 * a)) := by
      have := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 8 * a)
      linarith
    linarith
  unfold sa16r_g
  rw [hpre]
  have hC : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * a)) ^ (-((d : ℝ) / 2)) := by positivity
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * a)) ^ (-((d : ℝ) / 2)) *
        Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2)
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * a)) ^ (-((d : ℝ) / 2)) *
        (Real.exp (-(δ ^ 2 / (8 * a))) * Real.exp (-(1 / (4 * (2 * a))) * ‖z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a))) *
        ((4 * Real.pi * (2 * a)) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (4 * (2 * a))) * ‖z‖ ^ 2)) := by ring

lemma sa16r_g_tail {a : ℝ} (ha : 0 < a) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫⁻ z in {z : Euc d | δ ≤ ‖z‖}, ‖sa16r_g d a z‖ₑ ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a)))) := by
  have h2a : 0 < 2 * a := by positivity
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a))) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∫⁻ z in {z : Euc d | δ ≤ ‖z‖}, ‖sa16r_g d a z‖ₑ
      ≤ ∫⁻ z in {z : Euc d | δ ≤ ‖z‖}, ENNReal.ofReal (c * sa16r_g d (2 * a) z) := by
        refine setLIntegral_mono' (measurableSet_le measurable_const measurable_norm) fun z hz => ?_
        rw [Real.enorm_eq_ofReal (sa16r_g_pos ha z).le]
        exact ENNReal.ofReal_le_ofReal (by
          have := sa16r_g_tail_pointwise ha z hz hδ
          calc sa16r_g d a z ≤ c * sa16r_g d (2 * a) z := by rw [hc]; exact this)
    _ ≤ ∫⁻ z, ENNReal.ofReal (c * sa16r_g d (2 * a) z) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, c * sa16r_g d (2 * a) z) := by
        rw [ofReal_integral_eq_lintegral_ofReal ((sa16r_g_int h2a).const_mul c)
          (Eventually.of_forall fun z => mul_nonneg hc0 (sa16r_g_pos h2a z).le)]
    _ = ENNReal.ofReal c := by rw [integral_const_mul, sa16r_g_mass h2a, mul_one]

end Heat8

end HRS.Whole.AppendixA.Phase2SA16R
