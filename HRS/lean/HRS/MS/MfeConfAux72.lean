import HRS.MS.MfeConfAux71

/-!
# S.B.1, packet F8 (part 4): components of the truncated kernels and the derivatives of `G = k * ρ`

For `k` with `IsP4Kernel d s r₀ k` and `dk k j z = ∂_j k(z)`:

* `sb1_lv_gr_k`: `Sb1Gr k A`; `sb1_lv_gr_dk`: `Sb1Gr (dk k j) Lg`;
* `sb1_lv_dk_lip`: `∂_jk` is Lipschitz;
* `sb1_lv_dG_eq`: `∂_jG = cv (∂_jk) ρ`; `sb1_lv_hasFDerivAt_dG`: `∂_jG` is differentiable;
* `sb1_lv_ddG_lip`: `x ↦ ∂_j∂_jG(x)` is Lipschitz (integration by parts moves the derivative to `ρ`).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `∂_j k` -/
def sb1_lv_dk (k : Euc d → ℝ) (j : Fin d) (z : Euc d) : ℝ := fderiv ℝ k z (sb1e j)

theorem sb1_lv_gr_k {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs0 : 0 ≤ s) :
    ∃ A : ℝ, Sb1Gr k A := by
  obtain ⟨B, hB⟩ := p4k_bddAbove hk hs0
  refine ⟨max B 0, hk.smooth.continuous.measurable, fun z => ?_⟩
  have hl := hk.lower z
  have h0 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  rw [abs_le]
  constructor
  · linarith [le_max_right B 0]
  · linarith [hB z, le_max_left B 0]

theorem sb1_lv_dk_cont {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) (j : Fin d) : Continuous (sb1_lv_dk k j) :=
  (hk.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem sb1_lv_dk_bound {k : Euc d → ℝ} {Lg : ℝ} (h : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (j : Fin d) (z : Euc d) :
    |sb1_lv_dk k j z| ≤ Lg :=
  (sb1_apply_single_le _ j).trans (h z)

theorem sb1_lv_gr_dk {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {Lg : ℝ} (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (j : Fin d) :
    Sb1Gr (sb1_lv_dk k j) Lg := by
  refine ⟨(sb1_lv_dk_cont hk j).measurable, fun z => ?_⟩
  have h0 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  linarith [sb1_lv_dk_bound hL j z]

theorem sb1_lv_dk_diff {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) (j : Fin d) : Differentiable ℝ (sb1_lv_dk k j) :=
  ((hk.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)

theorem sb1_lv_dk_fderiv {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) (j : Fin d) (z v : Euc d) :
    fderiv ℝ (sb1_lv_dk k j) z v = fderiv ℝ (fderiv ℝ k) z v (sb1e j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ k) z :=
    ((hk.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  unfold sb1_lv_dk
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem sb1_lv_dk_fderiv_cont {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) (j : Fin d) :
    Continuous (fderiv ℝ (sb1_lv_dk k j)) := by
  have : ContDiff ℝ 1 (sb1_lv_dk k j) :=
    ((hk.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  exact this.continuous_fderiv (by norm_num)

theorem sb1_lv_dk_fderiv_bound {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (j : Fin d) (z : Euc d) :
    ‖fderiv ℝ (sb1_lv_dk k j) z‖ ≤ L2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg (fderiv ℝ (fderiv ℝ k) z)).trans (hL z)) fun v => ?_
  rw [sb1_lv_dk_fderiv hk]
  have h1 := (fderiv ℝ (fderiv ℝ k) z v).le_opNorm (sb1e j)
  have h2 := (fderiv ℝ (fderiv ℝ k) z).le_opNorm v
  have h3 : ‖sb1e j‖ = 1 := by simp [sb1e]
  rw [h3, mul_one] at h1
  calc |fderiv ℝ (fderiv ℝ k) z v (sb1e j)| = ‖fderiv ℝ (fderiv ℝ k) z v (sb1e j)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fderiv ℝ k) z v‖ := h1
    _ ≤ ‖fderiv ℝ (fderiv ℝ k) z‖ * ‖v‖ := h2
    _ ≤ L2 * ‖v‖ := mul_le_mul_of_nonneg_right (hL z) (norm_nonneg _)

theorem sb1_lv_dk_lip {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (j : Fin d) (z z' : Euc d) :
    |sb1_lv_dk k j z - sb1_lv_dk k j z'| ≤ L2 * ‖z - z'‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := sb1_lv_dk k j) (s := Set.univ) (C := L2)
    (fun w _ => sb1_lv_dk_diff hk j w) (fun w _ => sb1_lv_dk_fderiv_bound hk hL j w) convex_univ
    (Set.mem_univ z') (Set.mem_univ z)
  rw [← Real.norm_eq_abs]
  exact h

end HRS.MS.MfeConf
