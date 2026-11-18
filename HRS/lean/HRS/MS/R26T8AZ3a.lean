import HRS.MS.R26T8AZ2

/-!
# S8.2 T8A Z3a: derivative of the truncated source `G_N = (1 - chi(2^N .)) G`
`r26t8a_Z3a_diff_bound`: for `v ≠ 0`, `‖D G_N(v) - D G(v)‖ ≤ 1_{|v| < 3 (1/2)^N} (c1 |v|^{-s1} + c0 B1 2^N)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z3a_diff_bound {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {G : Euc d → ℝ}
    (hG1 : ContDiffOn ℝ 1 G {0}ᶜ) {c0 c1 s1 B1 : ℝ} (hc0 : ∀ w, w ≠ 0 → |G w| ≤ c0)
    (hc1 : ∀ w, w ≠ 0 → ‖fderiv ℝ G w‖ ≤ c1 * ‖w‖ ^ (-s1)) (hB1 : ∀ x, ‖fderiv ℝ chi x‖ ≤ B1)
    (N : ℕ) {v : Euc d} (hv : v ≠ 0) :
    ‖fderiv ℝ (fun w => (1 - chi ((2 : ℝ) ^ N • w)) * G w) v - fderiv ℝ G v‖ ≤
      (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)).indicator (fun v => c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N) v := by
  have hχ : ContDiff ℝ 1 (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) :=
    (hchi.1.of_le (by exact_mod_cast le_top)).comp (contDiff_const_smul _)
  have hGd : DifferentiableAt ℝ G v := (hG1.contDiffAt (isOpen_compl_singleton.mem_nhds hv)).differentiableAt (by norm_num)
  have hχd : DifferentiableAt ℝ (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) v := hχ.differentiable (by norm_num) v
  have hmul := fderiv_mul (c := fun w : Euc d => 1 - chi ((2 : ℝ) ^ N • w)) (d := G) (x := v)
    (differentiableAt_const _ |>.sub hχd) hGd
  have hsub : fderiv ℝ (fun w : Euc d => 1 - chi ((2 : ℝ) ^ N • w)) v =
      -fderiv ℝ (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) v := by
    rw [fderiv_const_sub]
  have hch : fderiv ℝ (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) v =
      (2 : ℝ) ^ N • fderiv ℝ chi ((2 : ℝ) ^ N • v) := by
    have hd1 : DifferentiableAt ℝ chi ((2 : ℝ) ^ N • v) := (hchi.1.differentiable (by simp)) _
    have := (hd1.hasFDerivAt).comp v ((hasFDerivAt_id v).const_smul ((2 : ℝ) ^ N))
    rw [show (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) = chi ∘ (fun w => (2 : ℝ) ^ N • w) from rfl, this.fderiv]
    ext u
    simp [ContinuousLinearMap.comp_apply, mul_comm]
  have hdiff : fderiv ℝ (fun w => (1 - chi ((2 : ℝ) ^ N • w)) * G w) v - fderiv ℝ G v =
      -(chi ((2 : ℝ) ^ N • v)) • fderiv ℝ G v - (G v) • ((2 : ℝ) ^ N • fderiv ℝ chi ((2 : ℝ) ^ N • v)) := by
    have hmul' : fderiv ℝ (fun w => (1 - chi ((2 : ℝ) ^ N • w)) * G w) v =
        (1 - chi ((2 : ℝ) ^ N • v)) • fderiv ℝ G v +
          G v • fderiv ℝ (fun w : Euc d => 1 - chi ((2 : ℝ) ^ N • w)) v := hmul
    rw [hmul', hsub, hch]
    rw [sub_smul, one_smul, neg_smul, smul_neg]
    abel
  by_cases hball : v ∈ ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)
  · rw [Set.indicator_of_mem hball, hdiff]
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 : ‖(chi ((2 : ℝ) ^ N • v))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hchi.2.2.1 _).1]; exact (hchi.2.2.1 _).2
    have h2 := hc1 v hv
    have h3 := hc0 v hv
    have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
    calc ‖-(chi ((2 : ℝ) ^ N • v)) • fderiv ℝ G v - (G v) • ((2 : ℝ) ^ N • fderiv ℝ chi ((2 : ℝ) ^ N • v))‖
        ≤ ‖-(chi ((2 : ℝ) ^ N • v)) • fderiv ℝ G v‖ + ‖(G v) • ((2 : ℝ) ^ N • fderiv ℝ chi ((2 : ℝ) ^ N • v))‖ :=
          norm_sub_le _ _
      _ ≤ 1 * (c1 * ‖v‖ ^ (-s1)) + c0 * ((2 : ℝ) ^ N * B1) := by
          refine add_le_add ?_ ?_
          · rw [norm_smul, norm_neg]
            exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N)]
            refine mul_le_mul h3 ?_ (by positivity) ((abs_nonneg _).trans h3)
            exact mul_le_mul_of_nonneg_left (hB1 _) (by positivity)
      _ = c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N := by ring
  · rw [Set.indicator_of_notMem hball]
    have hge : 3 * (1 / 2 : ℝ) ^ N ≤ ‖v‖ := by
      by_contra h
      exact hball (by rw [mem_ball_zero_iff]; linarith)
    have hbig : 2 < ‖(2 : ℝ) ^ N • v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) N]
    have hz1 : chi ((2 : ℝ) ^ N • v) = 0 := hchi.2.2.2.2 _ hbig.le
    have hz2 : fderiv ℝ chi ((2 : ℝ) ^ N • v) = 0 := by
      have : chi =ᶠ[𝓝 ((2 : ℝ) ^ N • v)] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hbig] with u hu
        exact hchi.2.2.2.2 u hu.le
      rw [this.fderiv_eq]; exact fderiv_const_apply 0
    rw [hdiff, hz1, hz2]; simp

end HRS.MS.R26T8A
