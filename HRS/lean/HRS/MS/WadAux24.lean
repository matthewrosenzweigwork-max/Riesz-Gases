import HRS.MS.WadAux23

/-!
# S8.3, packet D5''' (Route A): Lipschitz estimates from a mild form

* `s84_fderiv_le_of_lip`: a function that is `B`-Lipschitz near `x` and differentiable at `x` has
  `‖Du(x)‖ ≤ B`.
* `s84_lip_mild`: if `u = d0 + ∫_r^t f_s ds` on a convex set, with `‖Dd0‖ ≤ B0` and `‖Df_s‖ ≤ b(s)` there,
  then `u` is `(B0 + ∫b)`-Lipschitz on that set.  (No differentiation under the integral sign.)
* `s84_kernel_ii`: integrability of the singular kernel of `s84_kernel`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_fderiv_le_of_lip {u : Euc d → ℝ} {x : Euc d} {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (hu : DifferentiableAt ℝ u x)
    (hlip : ∀ y ∈ ball x ε, ∀ y' ∈ ball x ε, |u y' - u y| ≤ B * ‖y' - y‖) : ‖fderiv ℝ u x‖ ≤ B := by
  have h := hu.hasFDerivAt.le_of_lipschitzOn (ball_mem_nhds x hε) (C := B.toNNReal)
    (LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hB]
      exact hlip y' hy' y hy)
  rwa [Real.coe_toNNReal _ hB] at h

theorem s84_lip_mild {r t : ℝ} (hrt : r < t) {S : Set (Euc d)} (hS : Convex ℝ S)
    {u d0 : Euc d → ℝ} {f : ℝ → Euc d → ℝ} {B0 : ℝ} {b : ℝ → ℝ}
    (hmild : ∀ y ∈ S, u y = d0 y + ∫ s in r..t, f s y)
    (hint : ∀ y ∈ S, IntervalIntegrable (fun s => f s y) volume r t)
    (hd0 : ∀ y ∈ S, DifferentiableAt ℝ d0 y ∧ ‖fderiv ℝ d0 y‖ ≤ B0)
    (hf : ∀ s ∈ Set.Ioo r t, ∀ y ∈ S, DifferentiableAt ℝ (f s) y ∧ ‖fderiv ℝ (f s) y‖ ≤ b s)
    (hb : IntervalIntegrable b volume r t) :
    ∀ y ∈ S, ∀ y' ∈ S, |u y' - u y| ≤ (B0 + ∫ s in r..t, b s) * ‖y' - y‖ := by
  intro y hy y' hy'
  have e : u y' - u y = (d0 y' - d0 y) + ∫ s in r..t, (f s y' - f s y) := by
    rw [hmild y hy, hmild y' hy', intervalIntegral.integral_sub (hint y' hy') (hint y hy)]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 : |d0 y' - d0 y| ≤ B0 * ‖y' - y‖ := by
    have := hS.norm_image_sub_le_of_norm_fderiv_le (f := d0) (C := B0)
      (fun z hz => (hd0 z hz).1) (fun z hz => (hd0 z hz).2) hy hy'
    rwa [Real.norm_eq_abs] at this
  have hbn : IntervalIntegrable (fun s => b s * ‖y' - y‖) volume r t := hb.mul_const _
  have h2 : ‖∫ s in r..t, (f s y' - f s y)‖ ≤ ∫ s in r..t, b s * ‖y' - y‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hrt.le ?_ hbn
    filter_upwards [(Set.countable_singleton t).ae_notMem (volume : Measure ℝ)] with s hst hs
    have hs' : s ∈ Set.Ioo r t := ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have := hS.norm_image_sub_le_of_norm_fderiv_le (f := f s) (C := b s)
      (fun z hz => (hf s hs' z hz).1) (fun z hz => (hf s hs' z hz).2) hy hy'
    rwa [Real.norm_eq_abs] at this
  rw [intervalIntegral.integral_mul_const] at h2
  rw [← Real.norm_eq_abs (∫ s in r..t, (f s y' - f s y))]
  calc |d0 y' - d0 y| + ‖∫ s in r..t, (f s y' - f s y)‖ ≤ B0 * ‖y' - y‖ + (∫ s in r..t, b s) * ‖y' - y‖ :=
        add_le_add h1 h2
    _ = _ := by ring

/-- Integrability of the singular kernel. -/
theorem s84_kernel_ii {r t lam : ℝ} (hrt : r < t) :
    IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) MeasureTheory.volume r t := by
  set τ : ℝ := t - r with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  set m : ℝ := r + τ / 2 with hm
  have hrm : r < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm, hτ]; linarith
  have hI1 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) MeasureTheory.volume r m := by
    have h1 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume r m := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m - r) (r := -(3 / 4 : ℝ))
        (by norm_num)).comp_sub_right r
      simpa using this
    refine h1.mul_continuousOn ?_
    refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun s : ℝ => Real.exp (lam * (t - s))).continuousOn
    refine ContinuousOn.rpow_const (by fun_prop) fun s hs => Or.inl ?_
    rw [Set.uIcc_of_le hrm.le] at hs
    have : s ≤ m := hs.2
    have : t - s ≥ τ / 2 := by rw [hm] at this; linarith
    exact ne_of_gt (by linarith)
  have hI2 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) MeasureTheory.volume m t := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))
        MeasureTheory.volume m t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - m) (r := -(3 / 4 : ℝ))
        (by norm_num)).comp_sub_left t
      have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume m t := by
        simpa using this.symm
      exact h2.mul_continuousOn (by fun_prop : Continuous fun s : ℝ => Real.exp (lam * (t - s))).continuousOn
    refine h1.continuousOn_mul ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun s hs => Or.inl ?_
    rw [Set.uIcc_of_le hmt.le] at hs
    have : m ≤ s := hs.1
    have : s - r ≥ τ / 2 := by rw [hm] at this; linarith
    exact ne_of_gt (by linarith)
  exact hI1.trans hI2

end HRS.MS.Wad
