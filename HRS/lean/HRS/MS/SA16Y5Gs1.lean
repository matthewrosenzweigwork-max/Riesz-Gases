import HRS.MS.SA16Y5Cv4

/-!
# S.A.16 (SA16Y5) Gs1: the Gaussian semigroup law `g_a ⋆ g_b = g_{a+b}` (K3 helper)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Gs1
variable {d : ℕ}

lemma sa16y5_gauss_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x z : Euc d) :
    -(1 / (4 * a)) * ‖z‖ ^ 2 + -(1 / (4 * b)) * ‖x - z‖ ^ 2 =
      -(1 / (4 * (a + b))) * ‖x‖ ^ 2 +
        -((a + b) / (4 * a * b)) * ‖z - (a / (a + b)) • x‖ ^ 2 := by
  have hab : 0 < a + b := by linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inner_smul_right, real_inner_comm x z, real_inner_comm]
  field_simp
  ring

theorem sa16y5_g_conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : Euc d) :
    sa16r_cv (sa16r_g d a) (sa16r_g d b) x = sa16r_g d (a + b) x := by
  have hab : 0 < a + b := by linarith
  have hβ : 0 < (a + b) / (4 * a * b) := by positivity
  set β : ℝ := (a + b) / (4 * a * b) with hβdef
  set c : Euc d := (a / (a + b)) • x with hc
  have e1 : ∀ z : Euc d, sa16r_g d a z * sa16r_g d b (x - z) =
      ((4 * Real.pi * a) ^ (-((d : ℝ) / 2)) * (4 * Real.pi * b) ^ (-((d : ℝ) / 2)) *
        Real.exp (-(1 / (4 * (a + b))) * ‖x‖ ^ 2)) * Real.exp (-β * ‖z - c‖ ^ 2) := by
    intro z
    unfold sa16r_g
    have := sa16y5_gauss_exp ha hb x z
    calc _ = (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) * (4 * Real.pi * b) ^ (-((d : ℝ) / 2)) *
          (Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2) * Real.exp (-(1 / (4 * b)) * ‖x - z‖ ^ 2)) := by ring
      _ = _ := by
          rw [← Real.exp_add, this, Real.exp_add]
          ring
  unfold sa16r_cv
  simp_rw [e1]
  rw [integral_const_mul]
  have e2 : ∫ z : Euc d, Real.exp (-β * ‖z - c‖ ^ 2) = (Real.pi / β) ^ ((d : ℝ) / 2) := by
    rw [integral_sub_right_eq_self (fun z : Euc d => Real.exp (-β * ‖z‖ ^ 2)) c]
    exact sa16r_gauss_integral hβ
  rw [e2]
  unfold sa16r_g
  have hr : ∀ y : ℝ, 0 < y → (4 * Real.pi * y) ^ (-((d : ℝ) / 2)) = ((4 * Real.pi * y)⁻¹) ^ ((d : ℝ) / 2) := by
    intro y hy
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  have key : (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) * (4 * Real.pi * b) ^ (-((d : ℝ) / 2)) *
      (Real.pi / β) ^ ((d : ℝ) / 2) = (4 * Real.pi * (a + b)) ^ (-((d : ℝ) / 2)) := by
    rw [hr a ha, hr b hb, hr (a + b) hab, ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [hβdef]
    field_simp
  calc _ = ((4 * Real.pi * a) ^ (-((d : ℝ) / 2)) * (4 * Real.pi * b) ^ (-((d : ℝ) / 2)) *
        (Real.pi / β) ^ ((d : ℝ) / 2)) * Real.exp (-(1 / (4 * (a + b))) * ‖x‖ ^ 2) := by ring
    _ = _ := by rw [key]

end Gs1

end HRS.Whole.AppendixA.Phase2SA16R
