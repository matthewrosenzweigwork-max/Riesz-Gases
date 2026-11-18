import HRS.MS.SA16QPt1

/-!
# S.A.16 (SA16Y4) Io1: the first-derivative kernel for `0 ≤ s < d - 1` (the order-1 range of `iso` and `hilbert`)

The integration by parts `∫ g ∂_jφ(x-·) = ∫ K1_j φ(x-·)` and the weighted integrability of `g`, `K1` of the sub case
(`SA16QKer5`) were stated for `d ≥ 2`, `s ≤ d-2`; the proofs only use `1 ≤ d` and `s + 1 < d`.  Here they are restated for
`s < d - 1`, which contains the order-one part `d - 2 < s < d - 1` of `iso`/`hilbert` (`∂g ~ |y|^{-(s+1)}` locally integrable).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Io1
variable {d : ℕ}

lemma sa16y4io_m0_WI (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    sa16q_WI (sa16q_m0 d s) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine sa16q_WI_of_bounds hd (sa16q_m0_meas d s) (c := 3) (b := max s 1) (by norm_num)
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

lemma sa16y4io_m1_WI (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    sa16q_WI (sa16q_m1 d s) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg := sa16q_gam_pos hs
  refine sa16q_WI_of_bounds hd (sa16q_m1_meas d s) (c := sa16q_gam s) (b := s + 1) hg.le
    (by linarith) ?_ ?_
  · intro y hy hy1
    rw [Real.norm_of_nonneg (sa16q_m1_nonneg hs y)]
    exact le_rfl
  · intro y hy1
    rw [Real.norm_of_nonneg (sa16q_m1_nonneg hs y)]
    have := sa16q_rpow_le_one hy1 (b := s + 1) (by linarith)
    unfold sa16q_m1
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg y]) hg.le

lemma sa16y4io_g_WI (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    sa16q_WI (rieszKernel d s) := by
  have h := sa16y4io_m0_WI hd hs hs1
  unfold sa16q_WI at h ⊢
  refine h.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((sa16q_g_meas d s).norm.mul ((measurable_const.add measurable_norm).pow_const _)).aestronglyMeasurable
  · have hw : 0 ≤ (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hm : ‖rieszKernel d s y‖ ≤ ‖sa16q_m0 d s y‖ := by
      unfold sa16q_m0
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (by positivity))]
      linarith [norm_nonneg y]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    exact mul_le_mul_of_nonneg_right hm hw

theorem sa16y4io_ibp_g (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (j : Fin d) (x : Euc d)
    {φ : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ)) :
    ∫ y, rieszKernel d s y * fderiv ℝ φ (x - y) (EuclideanSpace.single j (1 : ℝ)) =
      ∫ y, sa16q_K1E s 0 j y * φ (x - y) := by
  refine sa16q_ibp_abstract hd j x hC hφd hφc hφ hφ'
    (fun n => sa16q_gE s (sa16q_eps n)) (fun n => sa16q_K1E s (sa16q_eps n) j)
    (rieszKernel d s) (sa16q_K1E s 0 j) (sa16q_m0 d s) (sa16q_m1 d s)
    (fun n => (sa16q_gE_cont s (sa16q_eps_pos n)).measurable)
    (fun n => sa16q_K1E_meas s _ j) (sa16q_g_meas d s) (sa16q_K1E_meas s 0 j)
    (sa16q_m0_meas d s) (sa16q_m1_meas d s) (sa16y4io_m0_WI hd hs hs1) (sa16y4io_m1_WI hd hs hs1)
    (fun n y => sa16q_gE_diff s (sa16q_eps_pos n) y)
    (fun n y => sa16q_gE_fderiv s (sa16q_eps_pos n) y j) ?_ ?_ (fun y hy => sa16q_gE_tendsto hy)
    (fun y hy => sa16q_K1E_tendsto j hy)
  · intro n y hy
    have := sa16q_gE_bound hs (sa16q_eps_pos n) (sa16q_eps_le_one n) hy
    simpa [sa16q_m0, Real.norm_eq_abs] using this
  · intro n y hy
    rw [Real.norm_eq_abs]
    exact sa16q_K1E_bound hs _ j hy
end Io1

end HRS.Whole.AppendixA.Phase2SA16Q
