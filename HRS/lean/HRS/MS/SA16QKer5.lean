import HRS.MS.SA16QKer4

/-!
# S.A.16 (SA16Q), E6 part 5: the two integration-by-parts identities

For `C¹` decaying `φ` (decay `(1+|z|)^{-(d+2)}` of `φ` and `∇φ`), `d ≥ 2`, `0 ≤ s ≤ d-2`:

* `sa16q_ibp_g`: `∫ g(y) ∂_jφ(x-y) dy = ∫ K1_j(y) φ(x-y) dy`;
* (`s < d-2`) `sa16q_ibp_K1`: `∫ K1_i(y) ∂_jφ(x-y) dy = ∫ K2_{ij}(y) φ(x-y) dy`,

with `K1 = sa16q_K1E s 0`, `K2 = sa16q_K2E s 0`.  Also the weighted integrability of all kernels involved.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section IbpInst
variable {d : ℕ}

lemma sa16q_g_meas (d : ℕ) (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, if_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [h, if_false]
    exact measurable_norm.pow_const _

lemma sa16q_gE_cont (s : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (sa16q_gE (d := d) s ε) :=
  continuous_iff_continuousAt.2 fun y => (sa16q_gE_diff s hε y).continuousAt

lemma sa16q_K1E_cont (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) : Continuous (sa16q_K1E s ε i) :=
  continuous_iff_continuousAt.2 fun y => (sa16q_K1E_diff s hε i y).continuousAt

lemma sa16q_K1E_meas (s ε : ℝ) (i : Fin d) : Measurable (sa16q_K1E s ε i) := by
  unfold sa16q_K1E
  have h1 : Measurable (fun y : Euc d => y i) := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  exact (measurable_const.mul h1).mul
    (((measurable_norm.pow_const 2).add measurable_const).pow_const _)

lemma sa16q_K2E_meas (s ε : ℝ) (i j : Fin d) : Measurable (sa16q_K2E s ε i j) := by
  unfold sa16q_K2E
  have h1 : Measurable (fun y : Euc d => y i) := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  have h2 : Measurable (fun y : Euc d => y j) := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable
  have h3 : Measurable (fun y : Euc d => ‖y‖ ^ 2 + ε ^ 2) := (measurable_norm.pow_const 2).add measurable_const
  exact ((measurable_const.mul (h3.pow_const _))).add
    ((((measurable_const.mul h1).mul h2)).mul (h3.pow_const _))

lemma sa16q_g_near {s : ℝ} (hs : 0 ≤ s) {y : Euc d} (hy : y ≠ 0) (hy1 : ‖y‖ < 1) :
    ‖rieszKernel d s y‖ ≤ ‖y‖ ^ (-(max s 1)) := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  rcases eq_or_ne s 0 with rfl | h
  · have h1 : Real.log ‖y‖ ≤ 0 := Real.log_nonpos hy0.le hy1.le
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hy0)
    rw [Real.log_inv] at h2
    have h3 : (max (0 : ℝ) 1) = 1 := by norm_num
    rw [h3, Real.rpow_neg_one, show rieszKernel d 0 y = -Real.log ‖y‖ from by simp [rieszKernel],
      Real.norm_eq_abs, abs_neg, abs_of_nonpos h1]
    linarith
  · rw [show rieszKernel d s y = ‖y‖ ^ (-s) from by simp [rieszKernel, h],
      Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1.le (by have := le_max_left s 1; linarith)

lemma sa16q_g_far {s : ℝ} (hs : 0 ≤ s) {y : Euc d} (hy1 : 1 ≤ ‖y‖) :
    ‖rieszKernel d s y‖ ≤ 1 + ‖y‖ := by
  have hy0 : 0 < ‖y‖ := by linarith
  rcases eq_or_ne s 0 with rfl | h
  · rw [show rieszKernel d 0 y = -Real.log ‖y‖ from by simp [rieszKernel], Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (Real.log_nonneg hy1)]
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    rw [show rieszKernel d s y = ‖y‖ ^ (-s) from by simp [rieszKernel, h],
      Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)]
    have := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith : -s ≤ 0)
    linarith

/-- the three majorants -/
def sa16q_m0 (d : ℕ) (s : ℝ) (y : Euc d) : ℝ := ‖rieszKernel d s y‖ + (1 + ‖y‖)
def sa16q_m1 (d : ℕ) (s : ℝ) (y : Euc d) : ℝ := sa16q_gam s * ‖y‖ ^ (-(s + 1))
def sa16q_m2 (d : ℕ) (s : ℝ) (y : Euc d) : ℝ := sa16q_gam s * (s + 3) * ‖y‖ ^ (-(s + 2))

lemma sa16q_m1_nonneg {s : ℝ} (hs : 0 ≤ s) (y : Euc d) : 0 ≤ sa16q_m1 d s y :=
  mul_nonneg (sa16q_gam_pos hs).le (Real.rpow_nonneg (norm_nonneg _) _)

lemma sa16q_m2_nonneg {s : ℝ} (hs : 0 ≤ s) (y : Euc d) : 0 ≤ sa16q_m2 d s y :=
  mul_nonneg (mul_nonneg (sa16q_gam_pos hs).le (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)

lemma sa16q_m0_meas (d : ℕ) (s : ℝ) : Measurable (sa16q_m0 d s) :=
  ((sa16q_g_meas d s).norm).add (measurable_const.add measurable_norm)

lemma sa16q_m1_meas (d : ℕ) (s : ℝ) : Measurable (sa16q_m1 d s) :=
  measurable_const.mul (measurable_norm.pow_const _)

lemma sa16q_m2_meas (d : ℕ) (s : ℝ) : Measurable (sa16q_m2 d s) :=
  measurable_const.mul (measurable_norm.pow_const _)

lemma sa16q_rpow_ge_one {y : Euc d} (hy : y ≠ 0) (hy1 : ‖y‖ < 1) {b : ℝ} (hb : 0 ≤ b) :
    1 ≤ ‖y‖ ^ (-b) := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1.le (by linarith)

lemma sa16q_rpow_le_one {y : Euc d} (hy1 : 1 ≤ ‖y‖) {b : ℝ} (hb : 0 ≤ b) : ‖y‖ ^ (-b) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)

lemma sa16q_m0_WI (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) :
    sa16q_WI (sa16q_m0 d s) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine sa16q_WI_of_bounds (by omega) (sa16q_m0_meas d s) (c := 3) (b := max s 1) (by norm_num)
    (by
      refine max_lt ?_ ?_ <;> linarith) ?_ ?_
  · intro y hy hy1
    have h1 := sa16q_g_near hs hy hy1
    have h2 := sa16q_rpow_ge_one hy hy1 (b := max s 1) (le_trans (by norm_num) (le_max_right s 1))
    have h3 : (1 + ‖y‖) ≤ 2 := by linarith
    unfold sa16q_m0
    rw [Real.norm_of_nonneg (by positivity)]
    linarith
  · intro y hy1
    have h1 := sa16q_g_far hs hy1
    unfold sa16q_m0
    rw [Real.norm_of_nonneg (by positivity)]
    linarith [norm_nonneg y]

lemma sa16q_m1_WI (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) :
    sa16q_WI (sa16q_m1 d s) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hg := sa16q_gam_pos hs
  refine sa16q_WI_of_bounds (by omega) (sa16q_m1_meas d s) (c := sa16q_gam s) (b := s + 1) hg.le
    (by linarith) ?_ ?_
  · intro y hy hy1
    rw [Real.norm_of_nonneg (sa16q_m1_nonneg hs y)]
    exact le_rfl
  · intro y hy1
    rw [Real.norm_of_nonneg (sa16q_m1_nonneg hs y)]
    have := sa16q_rpow_le_one hy1 (b := s + 1) (by linarith)
    unfold sa16q_m1
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg y]) hg.le

lemma sa16q_m2_WI (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s < (d : ℝ) - 2) :
    sa16q_WI (sa16q_m2 d s) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hg := sa16q_gam_pos hs
  refine sa16q_WI_of_bounds (by omega) (sa16q_m2_meas d s) (c := sa16q_gam s * (s + 3)) (b := s + 2)
    (mul_nonneg hg.le (by linarith)) (by linarith) ?_ ?_
  · intro y hy hy1
    rw [Real.norm_of_nonneg (sa16q_m2_nonneg hs y)]
    exact le_rfl
  · intro y hy1
    rw [Real.norm_of_nonneg (sa16q_m2_nonneg hs y)]
    have := sa16q_rpow_le_one hy1 (b := s + 2) (by linarith)
    have h3 : 0 ≤ sa16q_gam s * (s + 3) := mul_nonneg hg.le (by linarith)
    unfold sa16q_m2
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg y]) h3

theorem sa16q_ibp_g (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (j : Fin d) (x : Euc d)
    {φ : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ)) :
    ∫ y, rieszKernel d s y * fderiv ℝ φ (x - y) (EuclideanSpace.single j (1 : ℝ)) =
      ∫ y, sa16q_K1E s 0 j y * φ (x - y) := by
  refine sa16q_ibp_abstract (by omega) j x hC hφd hφc hφ hφ'
    (fun n => sa16q_gE s (sa16q_eps n)) (fun n => sa16q_K1E s (sa16q_eps n) j)
    (rieszKernel d s) (sa16q_K1E s 0 j) (sa16q_m0 d s) (sa16q_m1 d s)
    (fun n => (sa16q_gE_cont s (sa16q_eps_pos n)).measurable)
    (fun n => sa16q_K1E_meas s _ j) (sa16q_g_meas d s) (sa16q_K1E_meas s 0 j)
    (sa16q_m0_meas d s) (sa16q_m1_meas d s) (sa16q_m0_WI hd hs hs2) (sa16q_m1_WI hd hs hs2)
    (fun n y => sa16q_gE_diff s (sa16q_eps_pos n) y)
    (fun n y => sa16q_gE_fderiv s (sa16q_eps_pos n) y j) ?_ ?_ (fun y hy => sa16q_gE_tendsto hy)
    (fun y hy => sa16q_K1E_tendsto j hy)
  · intro n y hy
    have := sa16q_gE_bound hs (sa16q_eps_pos n) (sa16q_eps_le_one n) hy
    simpa [sa16q_m0, Real.norm_eq_abs] using this
  · intro n y hy
    rw [Real.norm_eq_abs]
    exact sa16q_K1E_bound hs _ j hy

theorem sa16q_ibp_K1 (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s < (d : ℝ) - 2) (i j : Fin d) (x : Euc d)
    {φ : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ)) :
    ∫ y, sa16q_K1E s 0 i y * fderiv ℝ φ (x - y) (EuclideanSpace.single j (1 : ℝ)) =
      ∫ y, sa16q_K2E s 0 i j y * φ (x - y) := by
  refine sa16q_ibp_abstract (by omega) j x hC hφd hφc hφ hφ'
    (fun n => sa16q_K1E s (sa16q_eps n) i) (fun n => sa16q_K2E s (sa16q_eps n) i j)
    (sa16q_K1E s 0 i) (sa16q_K2E s 0 i j) (sa16q_m1 d s) (sa16q_m2 d s)
    (fun n => sa16q_K1E_meas s _ i) (fun n => sa16q_K2E_meas s _ i j) (sa16q_K1E_meas s 0 i)
    (sa16q_K2E_meas s 0 i j) (sa16q_m1_meas d s) (sa16q_m2_meas d s)
    (sa16q_m1_WI hd hs (by linarith)) (sa16q_m2_WI hd hs hs2)
    (fun n y => sa16q_K1E_diff s (sa16q_eps_pos n) i y)
    (fun n y => sa16q_K1E_fderiv s (sa16q_eps_pos n) i j y) ?_ ?_
    (fun y hy => sa16q_K1E_tendsto i hy) (fun y hy => sa16q_K2E_tendsto i j hy)
  · intro n y hy
    rw [Real.norm_eq_abs]
    exact sa16q_K1E_bound hs _ i hy
  · intro n y hy
    rw [Real.norm_eq_abs]
    exact sa16q_K2E_bound hs _ i j hy

end IbpInst

end HRS.Whole.AppendixA.Phase2SA16Q
