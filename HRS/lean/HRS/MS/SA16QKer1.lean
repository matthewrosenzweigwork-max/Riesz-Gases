import HRS.MS.S16CzeAux2

/-!
# S.A.16 (SA16Q), E6 part 1: convolution with a weighted-integrable kernel

`sa16q_WI m`: `y ↦ ‖m y‖ (1+‖y‖)^{-(d+2)}` is integrable.  For such a kernel `m` and `φ` with
`‖φ z‖ ≤ C (1+‖z‖)^{-(d+2)}`:

* `sa16q_conv_integrable`: `y ↦ m y * φ (x - y)` is integrable (Peetre);
* `sa16q_hasFDerivAt_conv`: if moreover `φ` is `C^1` with `fderiv φ` of the same decay,
  `x ↦ ∫ m y * φ (x - y) dy` has derivative `∫ m y • fderiv φ (x - y) dy`.

Also `sa16q_WI_of_bounds`: a measurable kernel `|m| ≤ c|y|^{-b}` near `0` (`b < d`) and `|m| ≤ c (1+|y|)`
away from `0` is `sa16q_WI`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Conv
variable {d : ℕ}

/-- weighted integrability of a kernel -/
def sa16q_WI (m : Euc d → ℝ) : Prop :=
  Integrable (fun y : Euc d => ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)))

/-- decay of a function at the exponent `d+2` -/
def sa16q_Dec {F : Type*} [NormedAddCommGroup F] (C : ℝ) (f : Euc d → F) : Prop :=
  ∀ z : Euc d, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ))

lemma sa16q_WI_of_bounds (hd : 1 ≤ d) {m : Euc d → ℝ} (hm : Measurable m) {c b : ℝ} (hc : 0 ≤ c)
    (hb : b < d)
    (hnear : ∀ y : Euc d, y ≠ 0 → ‖y‖ < 1 → ‖m y‖ ≤ c * ‖y‖ ^ (-b))
    (hfar : ∀ y : Euc d, 1 ≤ ‖y‖ → ‖m y‖ ≤ c * (1 + ‖y‖)) : sa16q_WI m := by
  unfold sa16q_WI
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmeas : Measurable (fun y : Euc d => ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) :=
    hm.norm.mul ((measurable_const.add measurable_norm).pow_const _)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
      (by have : (0 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have h1 : IntegrableOn (fun y : Euc d => ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := c) (α := b)
      (by simpa using hd) (by simpa using hb) ?_ hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with y hy0 hy
    have hy1 : ‖y‖ < 1 := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    calc ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) ≤ ‖m y‖ * 1 := by gcongr; exact hw y
      _ ≤ _ := by rw [mul_one]; exact hnear y hy0 hy1
  have hr : (d : ℝ) < ((d + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hbd : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-(((d + 2 : ℕ) : ℝ) - 1))) volume :=
    integrable_one_add_norm (by simpa using hr)
  have h2 : IntegrableOn (fun y : Euc d => ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) (ball 0 1)ᶜ := by
    refine (hbd.const_mul c).integrableOn.mono' hmeas.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball.compl fun y hy => ?_
    have hy1 : 1 ≤ ‖y‖ := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))
        ≤ c * (1 + ‖y‖) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := by gcongr; exact hfar y hy1
      _ = c * (1 + ‖y‖) ^ (-(((d + 2 : ℕ) : ℝ) - 1)) := by
          rw [mul_assoc, ← Real.rpow_one_add' hpos.le (by push_cast; intro h0; linarith)]
          congr 2; ring
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

/-- Peetre's inequality for a decaying function -/
lemma sa16q_peetre {F : Type*} [NormedAddCommGroup F] {C : ℝ} {f : Euc d → F} (hf : sa16q_Dec C f)
    (hC : 0 ≤ C) (x y : Euc d) :
    ‖f (x - y)‖ ≤ C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := by
  have hx0 : 0 < 1 + ‖x‖ := by positivity
  have hy0 : 0 < 1 + ‖y‖ := by positivity
  have hz0 : 0 < 1 + ‖x - y‖ := by positivity
  have hxy : 1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖x - y‖) := by
    have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have := norm_sub_le x (x - y)
      simpa using this
    nlinarith [norm_nonneg x, norm_nonneg (x - y)]
  have hbc : (1 + ‖y‖) ^ (d + 2) ≤ (1 + ‖x‖) ^ (d + 2) * (1 + ‖x - y‖) ^ (d + 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hy0.le hxy _
  have ha : 0 < (1 + ‖x - y‖) ^ (d + 2) := by positivity
  have hb : 0 < (1 + ‖y‖) ^ (d + 2) := by positivity
  have key : ((1 + ‖x - y‖) ^ (d + 2))⁻¹ ≤ (1 + ‖x‖) ^ (d + 2) * ((1 + ‖y‖) ^ (d + 2))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ ha hb, one_mul]
    exact hbc
  have h2 : (1 + ‖x - y‖) ^ (-((d + 2 : ℕ) : ℝ)) ≤
      (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hz0.le, Real.rpow_neg hy0.le, Real.rpow_natCast, Real.rpow_natCast]
    exact key
  calc ‖f (x - y)‖ ≤ C * (1 + ‖x - y‖) ^ (-((d + 2 : ℕ) : ℝ)) := hf (x - y)
    _ ≤ C * ((1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by gcongr
    _ = _ := by ring

lemma sa16q_conv_integrable {m : Euc d → ℝ} (hm : Measurable m) (hWI : sa16q_WI m) {C : ℝ} (hC : 0 ≤ C)
    {φ : Euc d → ℝ} (hφc : Continuous φ) (hφ : sa16q_Dec C φ) (x : Euc d) :
    Integrable (fun y => m y * φ (x - y)) := by
  refine (hWI.const_mul (C * (1 + ‖x‖) ^ (d + 2))).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact hm.aestronglyMeasurable.mul (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_mul]
    have := sa16q_peetre hφ hC x y
    calc ‖m y‖ * ‖φ (x - y)‖ ≤ ‖m y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring

/-- differentiation under the integral sign for `x ↦ ∫ m y φ (x - y) dy` -/
theorem sa16q_hasFDerivAt_conv {m : Euc d → ℝ} (hm : Measurable m) (hWI : sa16q_WI m) {C : ℝ}
    (hC : 0 ≤ C) {φ : Euc d → ℝ} (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ)) (x₀ : Euc d) :
    HasFDerivAt (fun x => ∫ y, m y * φ (x - y)) (∫ y, m y • fderiv ℝ φ (x₀ - y)) x₀ := by
  have hφcont : Continuous φ := hφd.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
    (bound := fun y => (C * (2 + ‖x₀‖) ^ (d + 2)) * (‖m y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))))
    (F' := fun x y => m y • fderiv ℝ φ (x - y)) (ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    exact hm.aestronglyMeasurable.mul (hφcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact sa16q_conv_integrable hm hWI hC hφcont hφ x₀
  · exact hm.aestronglyMeasurable.smul (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun y x hx => ?_
    rw [norm_smul]
    have h1 := sa16q_peetre hφ' hC x y
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hx
      have h2 := norm_le_norm_add_norm_sub' x x₀
      linarith
    have h3 : (1 + ‖x‖) ^ (d + 2) ≤ (2 + ‖x₀‖) ^ (d + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc ‖m y‖ * ‖fderiv ℝ φ (x - y)‖
        ≤ ‖m y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by gcongr
      _ ≤ ‖m y‖ * (C * (2 + ‖x₀‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by gcongr
      _ = _ := by ring
  · exact hWI.const_mul _
  · refine Eventually.of_forall fun y x _ => ?_
    have h1 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const y
    have h2 := (hφd (x - y)).hasFDerivAt.comp x h1
    have h3 := h2.const_mul (m y)
    simpa using h3

lemma sa16q_conv_int_fderiv {m : Euc d → ℝ} (hm : Measurable m) (hWI : sa16q_WI m) {C : ℝ}
    (hC : 0 ≤ C) {φ : Euc d → ℝ} (hφc : Continuous (fderiv ℝ φ)) (hφ' : sa16q_Dec C (fderiv ℝ φ))
    (x : Euc d) : Integrable (fun y => m y • fderiv ℝ φ (x - y)) := by
  refine (hWI.const_mul (C * (1 + ‖x‖) ^ (d + 2))).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact hm.aestronglyMeasurable.smul (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    have := sa16q_peetre hφ' hC x y
    calc ‖m y‖ * ‖fderiv ℝ φ (x - y)‖
        ≤ ‖m y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by gcongr
      _ = _ := by ring

/-- the directional derivative of a convolution -/
theorem sa16q_fderiv_conv_apply {m : Euc d → ℝ} (hm : Measurable m) (hWI : sa16q_WI m) {C : ℝ}
    (hC : 0 ≤ C) {φ : Euc d → ℝ} (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ)) (x e : Euc d) :
    fderiv ℝ (fun x => ∫ y, m y * φ (x - y)) x e = ∫ y, m y * fderiv ℝ φ (x - y) e := by
  rw [(sa16q_hasFDerivAt_conv hm hWI hC hφd hφc hφ hφ' x).fderiv,
    ContinuousLinearMap.integral_apply (sa16q_conv_int_fderiv hm hWI hC hφc hφ' x) e]
  simp [smul_eq_mul]

end Conv

end HRS.Whole.AppendixA.Phase2SA16Q
