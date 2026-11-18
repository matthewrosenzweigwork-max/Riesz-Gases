import HRS.MS.SuppU2Aux5

/-!
# U2 auxiliary 6: iterated kernel-side derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_contDiffAt_iter {κ : Euc d → ℝ} (hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z)
    (m n : ℕ) {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ n (iteratedFDeriv ℝ m κ) z :=
  (hsm z hz).iteratedFDeriv_right (m := n) (i := m) (by simp)

lemma u2_rpow_le_of_le {r z p : ℝ} (hr : 0 < r) (hz : r ≤ z) (hp : p ≤ 0) :
    z ^ p ≤ r ^ p :=
  Real.rpow_le_rpow_of_nonpos hr hz hp

theorem u2_kernel_side {κ : Euc d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z)
    (hD : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-a - j))
    {r : ℝ} (hr : 0 < r) {g : Euc d → ℝ} (hg : Continuous g)
    (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0) {x0 : Euc d} (hx0 : 2 * r ≤ ‖x0‖) (j : ℕ) :
    ∀ x ∈ ball x0 (r / 2),
      iteratedFDeriv ℝ j (u2Conv κ g) x = ∫ y, g y • iteratedFDeriv ℝ j κ (x - y) := by
  induction j with
  | zero =>
    intro x _
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp, u2Conv]
    have h1 := LinearIsometry.integral_comp_comm (μ := (volume : Measure (Euc d)))
      (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toLinearIsometry
      (fun y => g y • κ (x - y))
    have h2 : ∫ z, κ z • g (x - z) = ∫ y, g y • κ (x - y) := by
      have := integral_sub_left_eq_self (fun z => κ z • g (x - z)) (volume : Measure (Euc d)) x
      rw [← this]
      congr 1
      funext y
      simp only [sub_sub_cancel, smul_eq_mul]
      ring
    rw [h2]
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, map_smul] at h1
    rw [← h1]
    simp [iteratedFDeriv_zero_eq_comp]
  | succ m ih =>
    intro x hx
    have hzr : ∀ z : Euc d, r / 2 ≤ ‖z‖ → z ≠ 0 := fun z hz =>
      norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hz)
    obtain ⟨Cm, hCm, hCm'⟩ := hD m
    obtain ⟨Cm1, hCm1, hCm1'⟩ := hD (m + 1)
    have hr2 : 0 < r / 2 := by linarith
    have hd := u2_ks_hasFDerivAt (iteratedFDeriv ℝ m κ) hr hg hsupp hx0
      (fun z hz => (u2_contDiffAt_iter hsm m 1 (hzr z hz)).differentiableAt (by simp))
      (fun z hz => by
        have h2 := u2_contDiffAt_iter hsm m 2 (hzr z hz)
        have : ContDiffAt ℝ 1 (fderiv ℝ (iteratedFDeriv ℝ m κ)) z :=
          h2.fderiv_right (by norm_num)
        exact this.continuousAt)
      (B0 := Cm * (r / 2) ^ (-a - m))
      (fun z hz => (hCm' z (hzr z hz)).trans (mul_le_mul_of_nonneg_left
        (u2_rpow_le_of_le hr2 hz (by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith)) hCm))
      (B1 := Cm1 * (r / 2) ^ (-a - ((m + 1 : ℕ) : ℝ)))
      (fun z hz => by
        rw [u2_norm_fderiv_iteratedFDeriv]
        exact (hCm1' z (hzr z hz)).trans (mul_le_mul_of_nonneg_left
          (u2_rpow_le_of_le hr2 hz (by have : (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)) hCm1))
      hx
    have hev : iteratedFDeriv ℝ m (u2Conv κ g) =ᶠ[𝓝 x]
        fun x' => ∫ y, g y • iteratedFDeriv ℝ m κ (x' - y) := by
      filter_upwards [IsOpen.mem_nhds isOpen_ball hx] with x' hx'
      exact ih x' hx'
    have hfd := hev.fderiv_eq (𝕜 := ℝ)
    rw [iteratedFDeriv_succ_eq_comp_left (f := u2Conv κ g)]
    simp only [Function.comp_apply]
    rw [hfd, hd.fderiv]
    have h1 := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).symm.toContinuousLinearEquiv
      (fun y => g y • fderiv ℝ (iteratedFDeriv ℝ m κ) (x - y))
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul] at h1
    rw [← h1]
    congr 1

theorem u2_kernel_side_norm {κ : Euc d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z)
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hDj : ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-a - j))
    (hD : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-a - j))
    {r : ℝ} (hr : 0 < r) {g : Euc d → ℝ} (hg : Continuous g)
    (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0) {x0 : Euc d} (hx0 : 2 * r ≤ ‖x0‖) :
    ‖iteratedFDeriv ℝ j (u2Conv κ g) x0‖ ≤ (C * r ^ (-a - j)) * ∫ y, ‖g y‖ := by
  have hgi : Integrable g volume := u2_integrable_of_support hg hsupp
  have hr0 : 0 < ‖x0‖ := by linarith
  rw [u2_kernel_side ha hsm hD hr hg hsupp hx0 j x0 (mem_ball_self (by linarith))]
  have hb : ∀ y : Euc d, ‖g y • iteratedFDeriv ℝ j κ (x0 - y)‖ ≤ ‖g y‖ * (C * r ^ (-a - j)) := by
    intro y
    rw [norm_smul]
    by_cases hy : ‖y‖ ≤ r
    · have h1 : r ≤ ‖x0 - y‖ := by
        have : ‖x0‖ ≤ ‖x0 - y‖ + ‖y‖ := by
          calc ‖x0‖ = ‖(x0 - y) + y‖ := by simp
            _ ≤ _ := norm_add_le _ _
        linarith
      have hz : x0 - y ≠ 0 := norm_pos_iff.mp (by linarith)
      refine mul_le_mul_of_nonneg_left ((hDj _ hz).trans (mul_le_mul_of_nonneg_left ?_ hC))
        (norm_nonneg _)
      refine u2_rpow_le_of_le hr h1 (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    · have : g y = 0 := hsupp y (by simpa using hy)
      simp [this]
  calc ‖∫ y, g y • iteratedFDeriv ℝ j κ (x0 - y)‖ ≤ ∫ y, ‖g y‖ * (C * r ^ (-a - j)) :=
        norm_integral_le_of_norm_le (hgi.norm.mul_const _) (Filter.Eventually.of_forall hb)
    _ = (C * r ^ (-a - j)) * ∫ y, ‖g y‖ := by rw [integral_mul_const]; ring

end HRS.Whole
