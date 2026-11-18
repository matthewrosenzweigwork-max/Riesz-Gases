import HRS.MH.ScreenedS3

/-!
# S16-CZE, part 1: `∂_i ∂_j (g * u) = g * ∂_i ∂_j u` for Schwartz `u` and `g = rieszKernel d (d-2)`

Packet S16-CZE (even Calderon-Zygmund `D² Δ⁻¹`, input E2 of S.A.16; `docs/CZ_PLAN.md`), calculus part.

Setting: `d ≥ 2`, `g = rieszKernel d ((d:ℝ) - 2)`, i.e. `g(x) = |x|^{2-d}` for `d ≥ 3` and `g(x) = -log|x|` for
`d = 2` (the only case of `s = d - 2 = 0`), and `HRS.Whole.convFun g u (x) = ∫ g(x - y) u(y) dy`, the convolution of the
repo (`HRS.Whole.convFun`).  For a real Schwartz function `u` this integral converges absolutely for every `x`
(no junk value): `g` is locally integrable (`|g| ≤ |y|^{-b}`, `b = max (d-2) 1 < d`, for `|y| < 1`) and
`|g(y)| ≤ 1 + |y|` for `|y| ≥ 1`.

Main results.

* `s16cze_conv_int`: `y ↦ g(y) • ψ(x - y)` is integrable for every Schwartz `ψ` (vector valued) and every `x`.
* `s16cze_hasFDerivAt_conv`: the function `x ↦ ∫ g(y) φ(x - y) dy = HRS.Whole.convFun g φ x` is Fréchet differentiable,
  with derivative `∫ g(y) • fderiv φ (x - y) dy` (differentiation under the integral sign with the
  `x`-independent majorant `‖g(y)‖ (1 + ‖y‖)^{-N}`, Peetre's inequality).
* `s16cze_second_deriv_conv`: for real Schwartz `u` and `i j`, the functions `HRS.Whole.convFun g u` and
  `y ↦ ∂_j (HRS.Whole.convFun g u) y` are differentiable everywhere (so the iterated `fderiv` below is not a junk
  value) and `∂_i ∂_j (HRS.Whole.convFun g u) = HRS.Whole.convFun g (∂_i ∂_j u)`, where `∂_j u = s16cze_pd u j` is the Schwartz
  function `lineDerivOp e_j u`.

Nothing is assumed beyond `2 ≤ d`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace HRS.S16Cze

open HRS.Whole

variable {d : ℕ}

/-- the exponent bounding `g` near `0`: `b = max (d-2) 1` -/
def s16cze_b (d : ℕ) : ℝ := max ((d : ℝ) - 2) 1

lemma s16cze_b_lt (hd : 2 ≤ d) : s16cze_b d < d := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold s16cze_b
  apply max_lt <;> linarith

lemma s16cze_g_small (hd : 2 ≤ d) {y : Euc d} (hy0 : y ≠ 0) (hy : ‖y‖ < 1) :
    ‖rieszKernel d ((d : ℝ) - 2) y‖ ≤ ‖y‖ ^ (-(s16cze_b d)) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold rieszKernel
  split_ifs with h
  · have hd2' : (d : ℝ) = 2 := by linarith
    have hb : s16cze_b d = 1 := by unfold s16cze_b; rw [hd2']; norm_num
    rw [hb, Real.rpow_neg_one, Real.norm_eq_abs, abs_neg]
    have h1 : Real.log ‖y‖ ≤ 0 := Real.log_nonpos hr.le hy.le
    rw [abs_of_nonpos h1]
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
    rw [Real.log_inv] at this
    linarith
  · have hb : s16cze_b d = (d : ℝ) - 2 := by
      unfold s16cze_b
      have hd3 : 3 ≤ d := by
        rcases Nat.lt_or_ge d 3 with h3 | h3
        · exfalso; apply h
          have : d = 2 := by omega
          rw [this]; norm_num
        · exact h3
      have hd3' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
      rw [max_eq_left (by linarith)]
    rw [hb, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]

lemma s16cze_g_large (hd : 2 ≤ d) {y : Euc d} (hy : 1 ≤ ‖y‖) :
    ‖rieszKernel d ((d : ℝ) - 2) y‖ ≤ 1 + ‖y‖ := by
  have hr : 0 < ‖y‖ := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold rieszKernel
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_neg]
    have h1 : 0 ≤ Real.log ‖y‖ := Real.log_nonneg hy
    rw [abs_of_nonneg h1]
    have := Real.log_le_sub_one_of_pos hr
    linarith
  · have hpos : (d : ℝ) - 2 > 0 := lt_of_le_of_ne (by linarith) (Ne.symm h)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
    have := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith : -((d : ℝ) - 2) ≤ 0)
    linarith

lemma s16cze_g_meas (d : ℕ) : Measurable (rieszKernel d ((d : ℝ) - 2)) := by
  by_cases h : (d : ℝ) - 2 = 0
  · have : rieszKernel d ((d : ℝ) - 2) = fun x => -Real.log ‖x‖ := by
      funext x; simp [rieszKernel, h]
    rw [this]
    exact (Real.measurable_log.comp measurable_norm).neg
  · have : rieszKernel d ((d : ℝ) - 2) = fun x => ‖x‖ ^ (-((d : ℝ) - 2)) := by
      funext x; simp [rieszKernel, h]
    rw [this]
    exact measurable_norm.pow_const _

/-- weighted integrability of `g` -/
lemma s16cze_g_int (hd : 2 ≤ d) {N : ℕ} (hN : d + 1 < N) :
    Integrable (fun y : Euc d => ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hmeas : Measurable (fun y : Euc d => ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ))) :=
    (s16cze_g_meas d).norm.mul ((measurable_const.add measurable_norm).pow_const _)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-(N : ℝ)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by simp)
  have h1 : IntegrableOn (fun y : Euc d => ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ)))
      (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := s16cze_b d)
      (by simpa using hd1) (by simpa using s16cze_b_lt hd) ?_ hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd1] with y hy0 hy
    have hy1 : ‖y‖ < 1 := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)), one_mul]
    calc ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ))
        ≤ ‖rieszKernel d ((d : ℝ) - 2) y‖ * 1 := by gcongr; exact hw y
      _ ≤ _ := by rw [mul_one]; exact s16cze_g_small hd hy0 hy1
  have hr : (d : ℝ) < (N : ℝ) - 1 := by
    have : ((d + 1 : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hN
    push_cast at this; linarith
  have hbd : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((N : ℝ) - 1))) volume :=
    integrable_one_add_norm (by simpa using hr)
  have h2 : IntegrableOn (fun y : Euc d => ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ)))
      (ball 0 1)ᶜ := by
    refine hbd.integrableOn.mono' hmeas.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball.compl fun y hy => ?_
    have hy1 : 1 ≤ ‖y‖ := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-(N : ℝ))
        ≤ (1 + ‖y‖) * (1 + ‖y‖) ^ (-(N : ℝ)) := by gcongr; exact s16cze_g_large hd hy1
      _ = (1 + ‖y‖) ^ (-((N : ℝ) - 1)) := by
          have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (by omega : 3 ≤ N)
          rw [← Real.rpow_one_add' hpos.le (by intro h0; linarith)]
          congr 1; ring
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

/-- Peetre-type weighted bound for Schwartz functions -/
lemma s16cze_weighted {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : 𝓢(Euc d, F))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Euc d, ‖ψ (x - y)‖ ≤ C * (1 + ‖x‖) ^ N * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  set C0 : ℝ := 2 ^ N * ((Finset.Iic (N, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hC0
  refine ⟨C0, by positivity, fun x y => ?_⟩
  have hz := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl ψ (x - y)
  rw [norm_iteratedFDeriv_zero] at hz
  have hpos : 0 < (1 + ‖y‖) ^ N := by positivity
  have hxy : 1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖x - y‖) := by
    have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have := norm_sub_le x (x - y)
      simpa using this
    nlinarith [norm_nonneg x, norm_nonneg (x - y)]
  have key : (1 + ‖y‖) ^ N * ‖ψ (x - y)‖ ≤ C0 * (1 + ‖x‖) ^ N := by
    calc (1 + ‖y‖) ^ N * ‖ψ (x - y)‖
        ≤ ((1 + ‖x‖) * (1 + ‖x - y‖)) ^ N * ‖ψ (x - y)‖ := by gcongr
      _ = (1 + ‖x‖) ^ N * ((1 + ‖x - y‖) ^ N * ‖ψ (x - y)‖) := by rw [mul_pow]; ring
      _ ≤ (1 + ‖x‖) ^ N * C0 := by gcongr
      _ = C0 * (1 + ‖x‖) ^ N := mul_comm _ _
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖ψ (x - y)‖ * (1 + ‖y‖) ^ N = (1 + ‖y‖) ^ N * ‖ψ (x - y)‖ := mul_comm _ _
    _ ≤ _ := key

lemma s16cze_conv_int (hd : 2 ≤ d) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : 𝓢(Euc d, F)) (x : Euc d) :
    Integrable (fun y : Euc d => rieszKernel d ((d : ℝ) - 2) y • ψ (x - y)) := by
  obtain ⟨C, hC0, hC⟩ := s16cze_weighted ψ (d + 2)
  refine ((s16cze_g_int hd (N := d + 2) (by omega)).const_mul (C * (1 + ‖x‖) ^ (d + 2))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (s16cze_g_meas d).aestronglyMeasurable.smul
      (ψ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    have := hC x y
    push_cast at this ⊢
    calc ‖rieszKernel d ((d : ℝ) - 2) y‖ * ‖ψ (x - y)‖
        ≤ ‖rieszKernel d ((d : ℝ) - 2) y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d : ℝ) + 2))) := by
          gcongr
      _ = _ := by ring

lemma s16cze_conv_swap (g φ : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convFun g φ x = ∫ y, g y * φ (x - y) := by
  unfold HRS.Whole.convFun
  have := integral_sub_left_eq_self (fun z : Euc d => g z * φ (x - z)) volume x
  simpa [sub_sub_cancel] using this

/-- differentiation under the integral sign -/
theorem s16cze_hasFDerivAt_conv (hd : 2 ≤ d) (φ : 𝓢(Euc d, ℝ)) (x₀ : Euc d) :
    HasFDerivAt (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) φ)
      (∫ y, rieszKernel d ((d : ℝ) - 2) y • fderiv ℝ φ (x₀ - y)) x₀ := by
  have hfun : HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) φ =
      fun x => ∫ y, rieszKernel d ((d : ℝ) - 2) y * φ (x - y) := funext (s16cze_conv_swap _ _)
  rw [hfun]
  set ψ : 𝓢(Euc d, Euc d →L[ℝ] ℝ) := SchwartzMap.fderivCLM ℝ (Euc d) ℝ φ with hψ
  have hψa : ∀ z, ψ z = fderiv ℝ φ z := fun z => SchwartzMap.fderivCLM_apply ℝ φ z
  obtain ⟨C, hC0, hC⟩ := s16cze_weighted ψ (d + 2)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
    (bound := fun y => (C * (2 + ‖x₀‖) ^ (d + 2)) *
      (‖rieszKernel d ((d : ℝ) - 2) y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))))
    (F' := fun x y => rieszKernel d ((d : ℝ) - 2) y • fderiv ℝ φ (x - y))
    (ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    exact (s16cze_g_meas d).aestronglyMeasurable.mul
      (φ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · simpa using s16cze_conv_int hd φ x₀
  · refine (s16cze_g_meas d).aestronglyMeasurable.smul ?_
    have : Continuous fun y : Euc d => ψ (x₀ - y) :=
      ψ.continuous.comp (continuous_const.sub continuous_id)
    simpa [hψa] using this.aestronglyMeasurable
  · refine Eventually.of_forall fun y x hx => ?_
    rw [norm_smul, ← hψa]
    have h1 := hC x y
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hx
      have h2 := norm_le_norm_add_norm_sub' x x₀
      linarith
    have h3 : (1 + ‖x‖) ^ (d + 2) ≤ (2 + ‖x₀‖) ^ (d + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc ‖rieszKernel d ((d : ℝ) - 2) y‖ * ‖ψ (x - y)‖
        ≤ ‖rieszKernel d ((d : ℝ) - 2) y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ ‖rieszKernel d ((d : ℝ) - 2) y‖ * (C * (2 + ‖x₀‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring
  · exact (s16cze_g_int hd (N := d + 2) (by omega)).const_mul _
  · refine Eventually.of_forall fun y x _ => ?_
    have h1 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const y
    have h2 := (φ.differentiableAt (x := x - y)).hasFDerivAt.comp x h1
    have h3 := h2.const_mul (rieszKernel d ((d : ℝ) - 2) y)
    simpa using h3

/-- directional derivative of `g * φ` -/
theorem s16cze_fderiv_conv (hd : 2 ≤ d) (φ : 𝓢(Euc d, ℝ)) (x e : Euc d) :
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) φ) x e =
      HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (fun z => fderiv ℝ φ z e) x := by
  rw [(s16cze_hasFDerivAt_conv hd φ x).fderiv, s16cze_conv_swap]
  have hint : Integrable (fun y : Euc d => rieszKernel d ((d : ℝ) - 2) y • fderiv ℝ φ (x - y)) := by
    have := s16cze_conv_int hd (SchwartzMap.fderivCLM ℝ (Euc d) ℝ φ) x
    simpa [SchwartzMap.fderivCLM_apply] using this
  rw [ContinuousLinearMap.integral_apply hint e]
  simp [smul_eq_mul]

/-- the coordinate derivative `∂_j u` of a real Schwartz function, as a Schwartz function -/
def s16cze_pd (u : 𝓢(Euc d, ℝ)) (j : Fin d) : 𝓢(Euc d, ℝ) :=
  LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u

lemma s16cze_pd_apply (u : 𝓢(Euc d, ℝ)) (j : Fin d) (x : Euc d) :
    s16cze_pd u j x = fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ)) := by
  unfold s16cze_pd
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- **`s16cze_second_deriv_conv`**: for `d ≥ 2`, real Schwartz `u` and `i j`: `HRS.Whole.convFun g u` and
`y ↦ ∂_j (HRS.Whole.convFun g u) y` are differentiable everywhere, `∂_j (g * u) = g * ∂_j u`, and
`∂_i ∂_j (g * u) = g * ∂_i ∂_j u`, with `g = rieszKernel d (d-2)`. -/
theorem s16cze_second_deriv_conv (hd : 2 ≤ d) (u : 𝓢(Euc d, ℝ)) (i j : Fin d) (x : Euc d) :
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) u) x ∧
    (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) u) y (EuclideanSpace.single j (1 : ℝ))) =
      HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd u j)) ∧
    DifferentiableAt ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) u) y
      (EuclideanSpace.single j (1 : ℝ))) x ∧
    fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) u) y
      (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
      HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd (s16cze_pd u j) i)) x := by
  have hfun : (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) u) y
      (EuclideanSpace.single j (1 : ℝ))) = HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd u j)) := by
    funext y
    rw [s16cze_fderiv_conv hd u y]
    congr 1
  refine ⟨(s16cze_hasFDerivAt_conv hd u x).differentiableAt, hfun, ?_, ?_⟩
  · rw [hfun]; exact (s16cze_hasFDerivAt_conv hd (s16cze_pd u j) x).differentiableAt
  · rw [hfun, s16cze_fderiv_conv hd (s16cze_pd u j) x]
    congr 1

end HRS.S16Cze
