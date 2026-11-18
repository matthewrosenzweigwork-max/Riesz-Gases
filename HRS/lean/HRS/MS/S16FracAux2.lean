import HRS.MS.S16CzeAux1

/-!
# S16-FRAC, part 2: derivatives of `g * F` and the integration-by-parts identity `B:eq:lp-top-ibp` (input E3)

Packet S16-FRAC (`docs/CZ_PLAN.md`, row S16-FRAC), calculus part.  Notation: `d ≥ 1`, `0 ≤ s < d`,
`g = rieszKernel d s` (`|x|^{-s}`, or `-log|x|` at `s = 0`), `convFun g F (x) = ∫ g(x-y) F(y) dy`
(`HRS.Whole.convFun`), `e_j = EuclideanSpace.single j 1`.

**Convention** (that of `S16CzeAux1/2`): `g` is locally integrable, so for a real Schwartz function `F` the
convolution `g * F` converges absolutely for every `x` (no junk value) and the "derivatives of `g` convolved with `F`"
of the supplement are the genuine Fréchet derivatives of `g * F`:
`∂_i g * F := ∂_i (g * F)`, `∂_i ∂_j g * F := ∂_i (∂_j (g * F))` (iterated `fderiv`, as in `s16cze_second_deriv_conv`).
This is the meaningful reading for every `0 ≤ s < d`: for `s ≥ d - 2` the kernels `∂_i∂_j g` are not locally
integrable (Calderon-Zygmund endpoint, `s = d - 2`, and the `p.v.` range), whereas `g * F` is a smooth function.

Results.

* `s16frac_hasFDerivAt_conv`, `s16frac_fderiv_conv`: for real Schwartz `φ`, `g * φ` is differentiable and
  `∂_e (g * φ) = g * ∂_e φ` (differentiation under the integral sign; generalises `s16cze_hasFDerivAt_conv`
  from `s = d - 2` to every `0 ≤ s < d`).
* `S16FracCb μ`: `μ` smooth with all derivatives bounded (`C_b^∞`; includes every `μ` of the S.A.16
  coefficient class); then `μ W`, `μ ∂_j W`, `(∂_j μ) W` are Schwartz for Schwartz `W`.
* `s16frac_ibp_first` (integrated form, no second derivative): for all `x`,
  `g * (μ ∂_j W) (x) = ∂_j (g * (μ W)) (x) - g * ((∂_j μ) W) (x)`.
* `s16frac_ibp` (**`B:eq:lp-top-ibp`**): `∂_i (g * (μ ∂_j W)) = ∂_i ∂_j (g * (μ W)) - ∂_i (g * ((∂_j μ) W))`
  at every point, with the differentiability of all four functions involved as part of the conclusion (so the
  iterated `fderiv` is not a junk value).
* `s16frac_lap_conv`: `Δ (g * u) = g * Δ u` for real Schwartz `u` (sum of `s16cze_pd` second derivatives; used by
  part 3 to read `Δg * u` as `g * Δ u`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace HRS.S16Frac

open HRS.Whole HRS.S16Cze

variable {d : ℕ} {s : ℝ}

/-! ### The kernel `g = rieszKernel d s`, `0 ≤ s < d` -/

/-- the exponent bounding `g` near `0` -/
def s16frac_b (d : ℕ) (s : ℝ) : ℝ := (s + d) / 2

lemma s16frac_b_pos (hs0 : 0 ≤ s) (hd : 1 ≤ d) : 0 < s16frac_b d s := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold s16frac_b; linarith

lemma s16frac_b_lt (hsd : s < d) : s16frac_b d s < d := by
  unfold s16frac_b; linarith

lemma s16frac_b_ge (hsd : s < d) : s ≤ s16frac_b d s := by
  unfold s16frac_b; linarith

lemma s16frac_g_small (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y : Euc d} (hy0 : y ≠ 0) (hy : ‖y‖ < 1) :
    ‖rieszKernel d s y‖ ≤ (1 / s16frac_b d s + 1) * ‖y‖ ^ (-(s16frac_b d s)) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hb := s16frac_b_pos hs0 hd
  have hrb : 0 < ‖y‖ ^ (-(s16frac_b d s)) := Real.rpow_pos_of_pos hr _
  have hinv : 1 / s16frac_b d s + 1 ≥ 1 := by
    have : 0 ≤ 1 / s16frac_b d s := by positivity
    linarith
  unfold rieszKernel
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_neg]
    have h1 : Real.log ‖y‖ ≤ 0 := Real.log_nonpos hr.le hy.le
    rw [abs_of_nonpos h1, ← Real.log_inv]
    have h2 := Real.log_le_rpow_div (x := ‖y‖⁻¹) (by positivity) hb
    rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] at h2
    calc Real.log ‖y‖⁻¹ ≤ ‖y‖ ^ (-(s16frac_b d s)) / s16frac_b d s := h2
      _ = (1 / s16frac_b d s) * ‖y‖ ^ (-(s16frac_b d s)) := by ring
      _ ≤ _ := by nlinarith
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
    have h2 : ‖y‖ ^ (-s) ≤ ‖y‖ ^ (-(s16frac_b d s)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hy.le (by linarith [s16frac_b_ge hsd])
    nlinarith

lemma s16frac_g_large (hs0 : 0 ≤ s) {y : Euc d} (hy : 1 ≤ ‖y‖) : ‖rieszKernel d s y‖ ≤ 1 + ‖y‖ := by
  have hr : 0 < ‖y‖ := by linarith
  unfold rieszKernel
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_neg]
    have h1 : 0 ≤ Real.log ‖y‖ := Real.log_nonneg hy
    rw [abs_of_nonneg h1]
    have := Real.log_le_sub_one_of_pos hr
    linarith
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
    have := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith : -s ≤ 0)
    linarith

lemma s16frac_g_meas (d : ℕ) (s : ℝ) : Measurable (rieszKernel d s) := by
  by_cases h : s = 0
  · have : rieszKernel d s = fun x => -Real.log ‖x‖ := by
      funext x; simp [rieszKernel, h]
    rw [this]
    exact (Real.measurable_log.comp measurable_norm).neg
  · have : rieszKernel d s = fun x => ‖x‖ ^ (-s) := by
      funext x; simp [rieszKernel, h]
    rw [this]
    exact measurable_norm.pow_const _

/-- weighted integrability of `g` -/
lemma s16frac_g_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : d + 1 < N) :
    Integrable (fun y : Euc d => ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ))) := by
  have hmeas : Measurable (fun y : Euc d => ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ))) :=
    (s16frac_g_meas d s).norm.mul ((measurable_const.add measurable_norm).pow_const _)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-(N : ℝ)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by simp)
  have h1 : IntegrableOn (fun y : Euc d => ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ)))
      (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1 / s16frac_b d s + 1) (α := s16frac_b d s)
      (by simpa using hd) (by simpa using s16frac_b_lt hsd) ?_ hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with y hy0 hy
    have hy1 : ‖y‖ < 1 := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    calc ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ))
        ≤ ‖rieszKernel d s y‖ * 1 := by gcongr; exact hw y
      _ ≤ _ := by rw [mul_one]; exact s16frac_g_small hd hs0 hsd hy0 hy1
  have hr : (d : ℝ) < (N : ℝ) - 1 := by
    have : ((d + 1 : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hN
    push_cast at this; linarith
  have hbd : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((N : ℝ) - 1))) volume :=
    integrable_one_add_norm (by simpa using hr)
  have h2 : IntegrableOn (fun y : Euc d => ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ)))
      (ball 0 1)ᶜ := by
    refine hbd.integrableOn.mono' hmeas.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball.compl fun y hy => ?_
    have hy1 : 1 ≤ ‖y‖ := by simpa using hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    have hpos : 0 < 1 + ‖y‖ := by positivity
    calc ‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-(N : ℝ))
        ≤ (1 + ‖y‖) * (1 + ‖y‖) ^ (-(N : ℝ)) := by gcongr; exact s16frac_g_large hs0 hy1
      _ = (1 + ‖y‖) ^ (-((N : ℝ) - 1)) := by
          have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (by omega : 3 ≤ N)
          rw [← Real.rpow_one_add' hpos.le (by intro h0; linarith)]
          congr 1; ring
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

lemma s16frac_conv_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ψ : 𝓢(Euc d, F)) (x : Euc d) :
    Integrable (fun y : Euc d => rieszKernel d s y • ψ (x - y)) := by
  obtain ⟨C, hC0, hC⟩ := s16cze_weighted ψ (d + 2)
  refine ((s16frac_g_int hd hs0 hsd (N := d + 2) (by omega)).const_mul (C * (1 + ‖x‖) ^ (d + 2))).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (s16frac_g_meas d s).aestronglyMeasurable.smul
      (ψ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    have := hC x y
    push_cast at this ⊢
    calc ‖rieszKernel d s y‖ * ‖ψ (x - y)‖
        ≤ ‖rieszKernel d s y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d : ℝ) + 2))) := by
          gcongr
      _ = _ := by ring

/-- differentiation under the integral sign (generalises `s16cze_hasFDerivAt_conv`) -/
theorem s16frac_hasFDerivAt_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (φ : 𝓢(Euc d, ℝ))
    (x₀ : Euc d) :
    HasFDerivAt (HRS.Whole.convFun (rieszKernel d s) φ)
      (∫ y, rieszKernel d s y • fderiv ℝ φ (x₀ - y)) x₀ := by
  have hfun : HRS.Whole.convFun (rieszKernel d s) φ =
      fun x => ∫ y, rieszKernel d s y * φ (x - y) := funext (s16cze_conv_swap _ _)
  rw [hfun]
  set ψ : 𝓢(Euc d, Euc d →L[ℝ] ℝ) := SchwartzMap.fderivCLM ℝ (Euc d) ℝ φ with hψ
  have hψa : ∀ z, ψ z = fderiv ℝ φ z := fun z => SchwartzMap.fderivCLM_apply ℝ φ z
  obtain ⟨C, hC0, hC⟩ := s16cze_weighted ψ (d + 2)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
    (bound := fun y => (C * (2 + ‖x₀‖) ^ (d + 2)) *
      (‖rieszKernel d s y‖ * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))))
    (F' := fun x y => rieszKernel d s y • fderiv ℝ φ (x - y))
    (ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    exact (s16frac_g_meas d s).aestronglyMeasurable.mul
      (φ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · simpa using s16frac_conv_int hd hs0 hsd φ x₀
  · refine (s16frac_g_meas d s).aestronglyMeasurable.smul ?_
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
    calc ‖rieszKernel d s y‖ * ‖ψ (x - y)‖
        ≤ ‖rieszKernel d s y‖ * (C * (1 + ‖x‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ ‖rieszKernel d s y‖ * (C * (2 + ‖x₀‖) ^ (d + 2) * (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring
  · exact (s16frac_g_int hd hs0 hsd (N := d + 2) (by omega)).const_mul _
  · refine Eventually.of_forall fun y x _ => ?_
    have h1 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const y
    have h2 := (φ.differentiableAt (x := x - y)).hasFDerivAt.comp x h1
    have h3 := h2.const_mul (rieszKernel d s y)
    simpa using h3

/-- directional derivative of `g * φ` -/
theorem s16frac_fderiv_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (φ : 𝓢(Euc d, ℝ)) (x e : Euc d) :
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) φ) x e =
      HRS.Whole.convFun (rieszKernel d s) (fun z => fderiv ℝ φ z e) x := by
  rw [(s16frac_hasFDerivAt_conv hd hs0 hsd φ x).fderiv, s16cze_conv_swap]
  have hint : Integrable (fun y : Euc d => rieszKernel d s y • fderiv ℝ φ (x - y)) := by
    have := s16frac_conv_int hd hs0 hsd (SchwartzMap.fderivCLM ℝ (Euc d) ℝ φ) x
    simpa [SchwartzMap.fderivCLM_apply] using this
  rw [ContinuousLinearMap.integral_apply hint e]
  simp [smul_eq_mul]

/-- linearity of the convolution on Schwartz functions (both integrands are integrable) -/
lemma s16frac_conv_sub (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (φ ψ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun z => φ z - ψ z) x =
      HRS.Whole.convFun (rieszKernel d s) φ x - HRS.Whole.convFun (rieszKernel d s) ψ x := by
  rw [s16cze_conv_swap, s16cze_conv_swap, s16cze_conv_swap]
  have h1 := s16frac_conv_int hd hs0 hsd φ x
  have h2 := s16frac_conv_int hd hs0 hsd ψ x
  simp only [smul_eq_mul] at h1 h2
  rw [← integral_sub h1 h2]
  congr 1; funext y; ring

lemma s16frac_conv_add (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (φ ψ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun z => φ z + ψ z) x =
      HRS.Whole.convFun (rieszKernel d s) φ x + HRS.Whole.convFun (rieszKernel d s) ψ x := by
  rw [s16cze_conv_swap, s16cze_conv_swap, s16cze_conv_swap]
  have h1 := s16frac_conv_int hd hs0 hsd φ x
  have h2 := s16frac_conv_int hd hs0 hsd ψ x
  simp only [smul_eq_mul] at h1 h2
  rw [← integral_add h1 h2]
  congr 1; funext y; ring

/-- `g * φ` is differentiable, and so is its directional derivative (again a convolution with a Schwartz function) -/
lemma s16frac_differentiable_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (φ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) φ) x :=
  (s16frac_hasFDerivAt_conv hd hs0 hsd φ x).differentiableAt

/-- the second derivative of `g * u` is `g * ∂_i ∂_j u` (all derivatives exist) -/
theorem s16frac_second_deriv_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (u : 𝓢(Euc d, ℝ))
    (i j : Fin d) (x : Euc d) :
    (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y (EuclideanSpace.single j (1 : ℝ))) =
      HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd u j)) ∧
    DifferentiableAt ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
      (EuclideanSpace.single j (1 : ℝ))) x ∧
    fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
      (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
      HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd (s16cze_pd u j) i)) x := by
  have hfun : (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
      (EuclideanSpace.single j (1 : ℝ))) = HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd u j)) := by
    funext y
    rw [s16frac_fderiv_conv hd hs0 hsd u y]
    congr 1
  refine ⟨hfun, ?_, ?_⟩
  · rw [hfun]; exact s16frac_differentiable_conv hd hs0 hsd (s16cze_pd u j) x
  · rw [hfun, s16frac_fderiv_conv hd hs0 hsd (s16cze_pd u j) x]
    congr 1

/-- **`Δ (g * u) = g * Δ u`** for real Schwartz `u`: the Laplacian of the convolution is the sum of the iterated
coordinate derivatives. -/
theorem s16frac_lap_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
      (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
      HRS.Whole.convFun (rieszKernel d s) (fun z => ∑ i : Fin d, s16cze_pd (s16cze_pd u i) i z) x := by
  have h : ∀ i : Fin d, fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) u) y
      (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
      HRS.Whole.convFun (rieszKernel d s) (⇑(s16cze_pd (s16cze_pd u i) i)) x :=
    fun i => (s16frac_second_deriv_conv hd hs0 hsd u i i x).2.2
  simp_rw [h]
  simp only [s16cze_conv_swap]
  rw [← integral_finsetSum]
  · congr 1; funext y; rw [Finset.mul_sum]
  · intro i _
    have := s16frac_conv_int hd hs0 hsd (s16cze_pd (s16cze_pd u i) i) x
    simpa [smul_eq_mul] using this

/-! ### Coefficients of class `C_b^∞` -/

/-- `μ` is smooth with all derivatives bounded (`C_b^∞`) -/
def S16FracCb (μ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ μ ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k μ x‖ ≤ C

lemma S16FracCb.temperate {μ : Euc d → ℝ} (hμ : S16FracCb μ) : μ.HasTemperateGrowth := by
  refine ⟨hμ.1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hμ.2 n
  exact ⟨0, C, fun x => by simpa using hC x⟩

lemma S16FracCb.deriv {μ : Euc d → ℝ} (hμ : S16FracCb μ) (e : Euc d) :
    S16FracCb (fun y => fderiv ℝ μ y e) := by
  have hc : ContDiff ℝ ∞ (fderiv ℝ μ) := hμ.1.fderiv_right (by simp)
  refine ⟨hc.clm_apply contDiff_const, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hμ.2 (k + 1)
  refine ⟨‖e‖ * C, fun x => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ μ) (c := e) (x := x) (N := ∞)
    (n := k) hc.contDiffAt (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (by gcongr; exact hC x)

/-- `μ W` as a Schwartz function -/
def s16frac_mul (μ : Euc d → ℝ) (hμ : S16FracCb μ) (W : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ μ W

lemma s16frac_mul_apply (μ : Euc d → ℝ) (hμ : S16FracCb μ) (W : 𝓢(Euc d, ℝ)) (x : Euc d) :
    s16frac_mul μ hμ W x = μ x * W x := by
  unfold s16frac_mul
  rw [SchwartzMap.smulLeftCLM_apply_apply hμ.temperate]
  rfl

/-- Leibniz: `∂_j (μ W) = (∂_j μ) W + μ ∂_j W` -/
lemma s16frac_pd_mul (μ : Euc d → ℝ) (hμ : S16FracCb μ) (W : 𝓢(Euc d, ℝ)) (j : Fin d) (x : Euc d) :
    s16cze_pd (s16frac_mul μ hμ W) j x =
      fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) * W x + μ x * s16cze_pd W j x := by
  rw [s16cze_pd_apply, s16cze_pd_apply]
  have hμd : DifferentiableAt ℝ μ x := (hμ.1.differentiable (by simp)) x
  have hfun : (⇑(s16frac_mul μ hμ W)) = fun y => μ y * W y := funext (s16frac_mul_apply μ hμ W)
  rw [hfun]
  have h : HasFDerivAt (fun y => μ y * W y) (μ x • fderiv ℝ W x + W x • fderiv ℝ μ x) x :=
    hμd.hasFDerivAt.mul (W.differentiableAt (x := x)).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### The integration-by-parts identity -/

/-- the integrated form of `B:eq:lp-top-ibp`: `g * (μ ∂_j W) = ∂_j (g * (μ W)) - g * ((∂_j μ) W)` -/
theorem s16frac_ibp_first (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {μ : Euc d → ℝ} (hμ : S16FracCb μ)
    (W : 𝓢(Euc d, ℝ)) (j : Fin d) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun z => μ z * s16cze_pd W j z) x =
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (s16frac_mul μ hμ W)) x (EuclideanSpace.single j (1 : ℝ)) -
        HRS.Whole.convFun (rieszKernel d s)
          (fun z => fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z) x := by
  rw [s16frac_fderiv_conv hd hs0 hsd]
  have hpd : (fun z => fderiv ℝ (s16frac_mul μ hμ W) z (EuclideanSpace.single j (1 : ℝ))) =
      fun z => s16cze_pd (s16frac_mul μ hμ W) j z := by
    funext z; rw [s16cze_pd_apply]
  rw [hpd]
  -- `μ ∂_j W` and `(∂_j μ) W` as Schwartz functions
  set A : 𝓢(Euc d, ℝ) := s16frac_mul μ hμ (s16cze_pd W j) with hA
  set B : 𝓢(Euc d, ℝ) := SchwartzMap.smulLeftCLM ℝ (fun y => fderiv ℝ μ y (EuclideanSpace.single j (1 : ℝ))) W
    with hB
  have hAa : ∀ z, A z = μ z * s16cze_pd W j z := fun z => s16frac_mul_apply μ hμ _ z
  have hBa : ∀ z, B z = fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z := fun z => by
    rw [hB, SchwartzMap.smulLeftCLM_apply_apply (hμ.deriv _).temperate]; rfl
  have h1 : (fun z => μ z * s16cze_pd W j z) = fun z => A z := funext fun z => (hAa z).symm
  have h2 : (fun z => fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z) = fun z => B z :=
    funext fun z => (hBa z).symm
  have h3 : (fun z => s16cze_pd (s16frac_mul μ hμ W) j z) = fun z => B z + A z := by
    funext z
    rw [s16frac_pd_mul, hAa, hBa]
  rw [h1, h2, h3, s16frac_conv_add hd hs0 hsd]
  ring

/-- **`B:eq:lp-top-ibp`** (supplement L10317), in the convention `∂_i g * F := ∂_i (g * F)`:
for `0 ≤ s < d`, `μ ∈ C_b^∞`, Schwartz `W`: the four functions below are differentiable at `x` (the iterated
`fderiv` are not junk values) and
`∂_i (g * (μ ∂_j W)) = ∂_i ∂_j (g * (μ W)) - ∂_i (g * ((∂_j μ) W))`. -/
theorem s16frac_ibp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {μ : Euc d → ℝ} (hμ : S16FracCb μ)
    (W : 𝓢(Euc d, ℝ)) (i j : Fin d) (x : Euc d) :
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => μ z * s16cze_pd W j z)) x ∧
    DifferentiableAt ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (s16frac_mul μ hμ W)) y
      (EuclideanSpace.single j (1 : ℝ))) x ∧
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s)
      (fun z => fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z)) x ∧
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => μ z * s16cze_pd W j z)) x
        (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (s16frac_mul μ hμ W)) y
        (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) -
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
        (fun z => fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z)) x (EuclideanSpace.single i (1 : ℝ)) := by
  set A : 𝓢(Euc d, ℝ) := s16frac_mul μ hμ (s16cze_pd W j) with hA
  set B : 𝓢(Euc d, ℝ) := SchwartzMap.smulLeftCLM ℝ (fun y => fderiv ℝ μ y (EuclideanSpace.single j (1 : ℝ))) W
    with hB
  have hAa : ∀ z, A z = μ z * s16cze_pd W j z := fun z => s16frac_mul_apply μ hμ _ z
  have hBa : ∀ z, B z = fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z := fun z => by
    rw [hB, SchwartzMap.smulLeftCLM_apply_apply (hμ.deriv _).temperate]; rfl
  have h1 : (fun z => μ z * s16cze_pd W j z) = fun z => A z := funext fun z => (hAa z).symm
  have h2 : (fun z => fderiv ℝ μ z (EuclideanSpace.single j (1 : ℝ)) * W z) = fun z => B z :=
    funext fun z => (hBa z).symm
  have hfirst : ∀ y, HRS.Whole.convFun (rieszKernel d s) (fun z => A z) y =
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (s16frac_mul μ hμ W)) y (EuclideanSpace.single j (1 : ℝ)) -
        HRS.Whole.convFun (rieszKernel d s) (fun z => B z) y := fun y => by
    have := s16frac_ibp_first hd hs0 hsd hμ W j y
    rwa [h1, h2] at this
  have hfun : (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (s16frac_mul μ hμ W)) y
      (EuclideanSpace.single j (1 : ℝ))) =
      fun y => HRS.Whole.convFun (rieszKernel d s) (fun z => A z) y +
        HRS.Whole.convFun (rieszKernel d s) (fun z => B z) y := by
    funext y; rw [hfirst y]; ring
  have hdA : DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => A z)) x :=
    s16frac_differentiable_conv hd hs0 hsd A x
  have hdB : DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => B z)) x :=
    s16frac_differentiable_conv hd hs0 hsd B x
  rw [h1, h2]
  refine ⟨hdA, ?_, hdB, ?_⟩
  · rw [hfun]; exact hdA.add hdB
  · have hadd : HasFDerivAt (fun y => HRS.Whole.convFun (rieszKernel d s) (fun z => A z) y +
        HRS.Whole.convFun (rieszKernel d s) (fun z => B z) y)
        (fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => A z)) x +
          fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (fun z => B z)) x) x :=
      hdA.hasFDerivAt.add hdB.hasFDerivAt
    rw [hfun, hadd.fderiv]
    simp

end HRS.S16Frac
