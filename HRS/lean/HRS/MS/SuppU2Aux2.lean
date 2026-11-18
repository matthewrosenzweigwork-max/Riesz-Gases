import HRS.MS.SuppU2Aux1

/-!
# U2 auxiliary 2: homogeneous kernels have derivative bounds `‖D^j κ(z)‖ ≤ C ‖z‖^{-a-j}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma u2_hom_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Euc d → E) (p : ℝ)
    (hG : ∀ w : Euc d, w ≠ 0 → DifferentiableAt ℝ G w)
    (hom : ∀ t : ℝ, 0 < t → ∀ w : Euc d, w ≠ 0 → G (t • w) = t ^ p • G w)
    {t : ℝ} (ht : 0 < t) {w : Euc d} (hw : w ≠ 0) :
    fderiv ℝ G (t • w) = t ^ (p - 1) • fderiv ℝ G w := by
  have h1 : HasFDerivAt (fun w' : Euc d => G (t • w'))
      ((fderiv ℝ G (t • w)).comp (t • ContinuousLinearMap.id ℝ (Euc d))) w :=
    HasFDerivAt.comp w (hG (t • w) (smul_ne_zero ht.ne' hw)).hasFDerivAt
      ((hasFDerivAt_id w).const_smul t)
  have h2 : HasFDerivAt (fun w' : Euc d => t ^ p • G w') (t ^ p • fderiv ℝ G w) w :=
    (hG w hw).hasFDerivAt.const_smul _
  have h3 : HasFDerivAt (fun w' : Euc d => G (t • w')) (t ^ p • fderiv ℝ G w) w := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hw] with y hy
    exact hom t ht y hy
  have h4 := h1.unique h3
  ext v
  have h5 := congrArg (fun L : Euc d →L[ℝ] E => L v) h4
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at h5
  rw [smul_apply, Real.rpow_sub_one ht.ne']
  have h6 : (t⁻¹ * t ^ p) • fderiv ℝ G w v = fderiv ℝ G (t • w) v := by
    rw [mul_smul, ← h5, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [← h6, div_eq_inv_mul]

lemma u2_iter_hom (κ : Euc d → ℝ) (a : ℝ) (hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z)
    (hom : ∀ t : ℝ, 0 < t → ∀ z : Euc d, z ≠ 0 → κ (t • z) = t ^ (-a) * κ z) (j : ℕ) :
    ∀ t : ℝ, 0 < t → ∀ z : Euc d, z ≠ 0 →
      iteratedFDeriv ℝ j κ (t • z) = t ^ (-a - j) • iteratedFDeriv ℝ j κ z := by
  induction j with
  | zero =>
    intro t ht z hz
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp, hom t ht z hz, Nat.cast_zero, sub_zero]
    ext m
    simp
  | succ j ih =>
    intro t ht z hz
    have hG : ∀ w : Euc d, w ≠ 0 → DifferentiableAt ℝ (iteratedFDeriv ℝ j κ) w := by
      intro w hw
      have := (hsm w hw).iteratedFDeriv_right (m := 1) (i := j) (by simp)
      exact this.differentiableAt (by simp)
    have h := u2_hom_fderiv (iteratedFDeriv ℝ j κ) (-a - j) hG ih ht hz
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Function.comp, h, map_smul]
    congr 2
    push_cast
    ring

lemma u2_iter_bound (κ : Euc d → ℝ) (a : ℝ) (hsm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z)
    (hom : ∀ t : ℝ, 0 < t → ∀ z : Euc d, z ≠ 0 → κ (t • z) = t ^ (-a) * κ z) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-a - j) := by
  have hcont : ContinuousOn (fun w : Euc d => ‖iteratedFDeriv ℝ j κ w‖) (sphere (0 : Euc d) 1) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0] at hw; simp at hw
    have := (hsm w hw0).iteratedFDeriv_right (m := 0) (i := j) (by simp)
    exact (this.continuousAt.norm).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euc d) 1).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : ‖z‖⁻¹ • z ∈ sphere (0 : Euc d) 1 := by
    simp [norm_smul, hzpos.ne']
  have hz'0 : ‖z‖⁻¹ • z ≠ 0 := smul_ne_zero (inv_pos.mpr hzpos).ne' hz
  have h := u2_iter_hom κ a hsm hom j ‖z‖ hzpos _ hz'0
  rw [smul_smul, mul_inv_cancel₀ hzpos.ne', one_smul] at h
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hzpos.le _), mul_comm]
  have := hC _ hz'
  simp only [norm_norm] at this
  exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) (Real.rpow_nonneg hzpos.le _)

lemma u2_integrableOn_ball_rpow (hd : 1 ≤ d) {a : ℝ} (ha0 : 0 < a) (had : a < d) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-a)) (ball (0 : Euc d) 1) volume := by
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using (by omega : 0 < d)
  have hF := integrableOn_fun_norm_addHaar (volume : Measure (Euc d)) (f := fun r : ℝ => r ^ (-a))
    (r := 1)
  rw [hF]
  simp only [finrank_euclideanSpace_fin]
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ ((d : ℝ) - 1 - a)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h1
  refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  show y ^ ((d : ℝ) - 1 - a) = y ^ (d - 1) • y ^ (-a)
  rw [smul_eq_mul, show (d : ℝ) - 1 - a = ((d - 1 : ℕ) : ℝ) + (-a) by
    rw [Nat.cast_sub hd]; push_cast; ring, Real.rpow_add hy0, Real.rpow_natCast]

end HRS.Whole
