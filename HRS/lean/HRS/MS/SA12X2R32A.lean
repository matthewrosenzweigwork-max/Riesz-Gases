import HRS.MH.AdjRdE3R3

/-!
# S.A.12 R32 (SA12X2), part A: the missing L1 estimate for the spill kernel derivative

`Kf_r = r3Kf d s r` satisfies `Kf_r(h) = r^(-s) F1(r⁻¹ h)` and `|∇F1(k) w| ≤ C ‖w‖ (1+|k|)^(-(s+1))`.
Hence `∫_{|h| ≤ R₀} |∂_w Kf_r| ≤ C (1+R₀) r^(-(s+2-d))` uniformly for `0 < r ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

/-- Far-field directional derivative bound for the Riesz kernel. -/
theorem sa12x2_kernel_fderiv_far {s : ℝ} (hs0 : 0 ≤ s) {k : Euc d} (hk : 2 < ‖k‖) (w : Euc d) :
    |fderiv ℝ (rieszKernel d s) k w| ≤
      movtr_sigma s * 2 ^ (s + 1) * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by
  have hk0 : k ≠ 0 := by
    intro h; rw [h, norm_zero] at hk; linarith
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
  have hgrad : fderiv ℝ (rieszKernel d s) k w = inner ℝ (rieszKernelGrad d s k) w := by
    unfold rieszKernelGrad gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have hn := movtr_rieszKernelGrad_norm s hs0 hk0
  have hσ : 0 ≤ movtr_sigma s := by
    unfold movtr_sigma; split_ifs <;> linarith
  have hpow : ‖k‖ ^ (-s - 1) ≤ 2 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) := by
    have h1 : (2 * ‖k‖) ^ (-(s + 1)) ≤ (1 + ‖k‖) ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hkpos.le] at h1
    have h2 : (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-(s + 1)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have e : -s - 1 = -(s + 1) := by ring
    rw [e]
    calc ‖k‖ ^ (-(s + 1)) = 2 ^ (s + 1) * ((2 : ℝ) ^ (-(s + 1)) * ‖k‖ ^ (-(s + 1))) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) := by
          gcongr
  calc |fderiv ℝ (rieszKernel d s) k w| = |inner ℝ (rieszKernelGrad d s k) w| := by rw [hgrad]
    _ ≤ ‖rieszKernelGrad d s k‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ = movtr_sigma s * ‖k‖ ^ (-s - 1) * ‖w‖ := by rw [hn]
    _ ≤ movtr_sigma s * (2 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1))) * ‖w‖ := by
          gcongr
    _ = movtr_sigma s * 2 ^ (s + 1) * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by ring

/-- Uniform directional gradient bound for `F1 = r3F1 d s`. -/
theorem sa12x2_F1_grad_bound {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ (k w : Euc d),
      |fderiv ℝ (r3F1 d s) k w| ≤ CF * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by
  have hF : ContDiff ℝ ∞ (r3F1 d s) := r3F1_contDiff
  have hcont : Continuous (fun k : Euc d => ‖fderiv ℝ (r3F1 d s) k‖) :=
    (hF.continuous_fderiv (by simp)).norm
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Euc d) 2).exists_bound_of_continuousOn
    hcont.continuousOn
  have hσ : 0 ≤ movtr_sigma s := by
    unfold movtr_sigma; split_ifs <;> linarith
  refine ⟨movtr_sigma s * 2 ^ (s + 1) + max M0 0 * 3 ^ (s + 1), by positivity, ?_⟩
  intro k w
  by_cases hk : 2 < ‖k‖
  · have hev : r3F1 d s =ᶠ[𝓝 k] fun y => rieszKernel d s y + (-r3c1 s) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hk] with y hy
      unfold r3F1
      rw [r3Bump_zero hy.le]; ring
    have hfe : fderiv ℝ (r3F1 d s) k = fderiv ℝ (rieszKernel d s) k := by
      rw [hev.fderiv_eq, fderiv_add_const]
    rw [hfe]
    have h1 := sa12x2_kernel_fderiv_far hs0 hk w
    have hX : 0 ≤ (1 + ‖k‖) ^ (-(s + 1)) := by positivity
    have hM : 0 ≤ max M0 0 * 3 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) * ‖w‖ := by
      have : (0:ℝ) ≤ max M0 0 := le_max_right _ _
      positivity
    nlinarith [norm_nonneg w]
  · have hk2 : ‖k‖ ≤ 2 := not_lt.1 hk
    have hb : |fderiv ℝ (r3F1 d s) k w| ≤ ‖fderiv ℝ (r3F1 d s) k‖ * ‖w‖ := by
      rw [← Real.norm_eq_abs]
      exact ContinuousLinearMap.le_opNorm _ _
    have hMk : ‖fderiv ℝ (r3F1 d s) k‖ ≤ max M0 0 := by
      refine le_max_of_le_left ?_
      have := hM0 k (mem_closedBall_zero_iff.2 hk2)
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
    have hX3 : (3 : ℝ) ^ (-(s + 1)) ≤ (1 + ‖k‖) ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h3 : (1 : ℝ) ≤ 3 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) := by
      have h2 : (3 : ℝ) ^ (s + 1) * (3 : ℝ) ^ (-(s + 1)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc (1 : ℝ) = 3 ^ (s + 1) * (3 : ℝ) ^ (-(s + 1)) := h2.symm
        _ ≤ 3 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) := by gcongr
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hMX : 0 ≤ movtr_sigma s * 2 ^ (s + 1) * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by
      positivity
    calc |fderiv ℝ (r3F1 d s) k w| ≤ ‖fderiv ℝ (r3F1 d s) k‖ * ‖w‖ := hb
      _ ≤ max M0 0 * ‖w‖ := by gcongr
      _ ≤ max M0 0 * ‖w‖ * (3 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1))) := by
          have : (0:ℝ) ≤ max M0 0 * ‖w‖ := by
            have : (0:ℝ) ≤ max M0 0 := le_max_right _ _
            positivity
          nlinarith
      _ = max M0 0 * 3 ^ (s + 1) * (1 + ‖k‖) ^ (-(s + 1)) * ‖w‖ := by ring
      _ ≤ (movtr_sigma s * 2 ^ (s + 1) + max M0 0 * 3 ^ (s + 1)) * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by
          have hX : 0 ≤ (1 + ‖k‖) ^ (-(s + 1)) := by positivity
          have : 0 ≤ movtr_sigma s * 2 ^ (s + 1) * ‖w‖ * (1 + ‖k‖) ^ (-(s + 1)) := by positivity
          nlinarith [le_max_right M0 0]

end HRS.MH.AdjointRd.Phase2SA12
