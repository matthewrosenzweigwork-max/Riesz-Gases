import HRS.MS.ThmDefs
import HRS.Whole.Q34Aux2

/-!
# THM-0: Gaussian facts, convolution bounds and a.e.-invariance for the THM core

Namespace `HRS.MS.Thm`; helper lemmas carry the prefix `t012_`.

Contents:

* `gaussianComparison_isProbDensity` (`0 < a`, `0 < β`; the hypothesis `1 ≤ d` of the packet sketch is
  not needed), `gaussianComparison_pos`;
* abstract convolution bounds for a kernel `K` with (K1): `conv_bound_of_le`, `t012_prod_integrable`,
  `t012_integrable_mul_log_div_of_le`;
* `riesz_conv_gaussian_bound` (K1 for `K x y = g (x - y)`, `r = γ`, `0 < s < d`),
  `hasFiniteFreeEnergy_of_le`, `convMeasure_withDensityReal`, `convMeasure_bound_of_le`;
* a.e.-invariance: `convMeasure_congr_ae`, `freeEnergy_congr_ae`, `hasFiniteFreeEnergy_congr_ae`.

Every statement carries the integrability / measurability hypotheses that exclude the Bochner junk value `0`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-! ### Elementary helpers -/

/-- A nonnegative measurable function with small lintegral is integrable, and its integral is bounded. -/
theorem t012_int_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hm : Measurable f) (h0 : ∀ x, 0 ≤ f x) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ c := by
  have hne : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (ae_of_all _ h0)).1 hne
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)
  exact (ENNReal.ofReal_le_ofReal_iff hc0).1 (h1 ▸ hc)

/-- `|a log a| ≤ 1 + M²` for `0 ≤ a ≤ M`. -/
theorem t012_abs_mul_log_le {a M : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) : |a * Real.log a| ≤ 1 + M ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp; positivity
  · rcases le_total a 1 with h1 | h1
    · have := Real.abs_log_mul_self_lt a hpos h1
      rw [mul_comm]; nlinarith [sq_nonneg M]
    · have hlog0 : 0 ≤ Real.log a := Real.log_nonneg h1
      have hlog1 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos hpos
      rw [abs_of_nonneg (mul_nonneg ha hlog0)]
      have : a * Real.log a ≤ a * a := by nlinarith
      nlinarith

/-- Measurability of `x ↦ ∫ K x y μ y dy`. -/
theorem t012_measurable_conv {K : Euc d → Euc d → ℝ} (hK : Measurable (Function.uncurry K))
    {μ : Euc d → ℝ} (hμ : Measurable μ) : Measurable fun x => ∫ y, K x y * μ y := by
  have : StronglyMeasurable (Function.uncurry fun x y => K x y * μ y) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hK.mul (hμ.comp measurable_snd))
  exact (this.integral_prod_right (ν := volume)).measurable

/-! ### Abstract convolution bounds (K1) -/

theorem t012_measurable_K_left {K : Euc d → Euc d → ℝ} (hK : Measurable (Function.uncurry K))
    (x : Euc d) : Measurable (K x) :=
  hK.comp (measurable_prodMk_left (m := inferInstance))

/-- `K * ρ ≤ M B` for `0 ≤ ρ ≤ M r` under (K1): integrability and the bound at every point. -/
theorem conv_bound_of_le {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}
    (hK : Measurable (Function.uncurry K)) (hnn : ∀ x y, 0 ≤ K x y)
    (hk1 : ∀ x, Integrable (fun y => K x y * r y) ∧ ∫ y, K x y * r y ≤ B)
    {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hM0 : 0 ≤ M)
    (hρM : ∀ y, ρ y ≤ M * r y) (x : Euc d) :
    Integrable (fun y => K x y * ρ y) ∧ 0 ≤ ∫ y, K x y * ρ y ∧ ∫ y, K x y * ρ y ≤ M * B := by
  have hpt : ∀ y, K x y * ρ y ≤ M * (K x y * r y) := fun y => by
    calc K x y * ρ y ≤ K x y * (M * r y) := mul_le_mul_of_nonneg_left (hρM y) (hnn x y)
      _ = M * (K x y * r y) := by ring
  have hint : Integrable (fun y => K x y * ρ y) := by
    refine Integrable.mono' ((hk1 x).1.const_mul M)
      ((t012_measurable_K_left hK x).mul hρm).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn x y) (hρ0 y))]
    exact hpt y
  refine ⟨hint, integral_nonneg fun y => mul_nonneg (hnn x y) (hρ0 y), ?_⟩
  calc ∫ y, K x y * ρ y ≤ ∫ y, M * (K x y * r y) :=
        integral_mono hint ((hk1 x).1.const_mul M) hpt
    _ = M * ∫ y, K x y * r y := integral_const_mul _ _
    _ ≤ M * B := mul_le_mul_of_nonneg_left (hk1 x).2 hM0

/-- Absolute integrability of `K(x,y) f(x) h(y)` on the product when `f ∈ L¹` and `|h| ≤ M r`. -/
theorem t012_prod_integrable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}
    (hK : Measurable (Function.uncurry K)) (hnn : ∀ x y, 0 ≤ K x y) (hr0 : ∀ y, 0 ≤ r y)
    (hk1 : ∀ x, Integrable (fun y => K x y * r y) ∧ ∫ y, K x y * r y ≤ B)
    {f h : Euc d → ℝ} (hfm : Measurable f) (hf : Integrable f) (hhm : Measurable h)
    (hM0 : 0 ≤ M) (hhM : ∀ y, |h y| ≤ M * r y) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2)
      ((volume : Measure (Euc d)).prod volume) := by
  have hB : 0 ≤ B :=
    le_trans (integral_nonneg fun y => mul_nonneg (hnn 0 y) (hr0 y)) (hk1 0).2
  have hmeas : Measurable fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2 :=
    (hK.mul (hfm.comp measurable_fst)).mul (hhm.comp measurable_snd)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  have hpt : ∀ x y, ‖K x y * f x * h y‖ ≤ (|f x| * M) * (K x y * r y) := fun x y => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hnn x y)]
    calc K x y * |f x| * |h y| ≤ K x y * |f x| * (M * r y) :=
          mul_le_mul_of_nonneg_left (hhM y) (mul_nonneg (hnn x y) (abs_nonneg _))
      _ = (|f x| * M) * (K x y * r y) := by ring
  refine ⟨ae_of_all _ fun x => ?_, ?_⟩
  · refine Integrable.mono' ((hk1 x).1.const_mul (|f x| * M)) ?_ (ae_of_all _ fun y => hpt x y)
    have : Measurable fun y => K x y * f x * h y :=
      ((t012_measurable_K_left hK x).mul measurable_const).mul hhm
    exact this.aestronglyMeasurable
  · have hm2 : AEStronglyMeasurable (fun x => ∫ y, ‖K x y * f x * h y‖) volume :=
      (hmeas.norm.aestronglyMeasurable).integral_prod_right'
    refine Integrable.mono' (hf.norm.const_mul (M * B)) hm2 (ae_of_all _ fun x => ?_)
    have h1 : ∫ y, ‖K x y * f x * h y‖ ≤ ∫ y, (|f x| * M) * (K x y * r y) := by
      refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
        ((hk1 x).1.const_mul _) (ae_of_all _ fun y => hpt x y)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    calc ∫ y, ‖K x y * f x * h y‖ ≤ ∫ y, (|f x| * M) * (K x y * r y) := h1
      _ = (|f x| * M) * ∫ y, K x y * r y := integral_const_mul _ _
      _ ≤ (|f x| * M) * B := mul_le_mul_of_nonneg_left (hk1 x).2 (mul_nonneg (abs_nonneg _) hM0)
      _ = M * B * ‖f x‖ := by rw [Real.norm_eq_abs]; ring

/-- `ρ log (ρ / r)` is integrable when `0 ≤ ρ ≤ M r`, `r > 0` integrable. -/
theorem t012_integrable_mul_log_div_of_le {r : Euc d → ℝ} (hr : Integrable r)
    (hrp : ∀ x, 0 < r x) (hrm : Measurable r) {ρ : Euc d → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {M : ℝ} (hρM : ∀ x, ρ x ≤ M * r x) :
    Integrable (fun x => ρ x * Real.log (ρ x / r x)) := by
  have hmeas : Measurable fun x => ρ x * Real.log (ρ x / r x) :=
    hρm.mul (Real.measurable_log.comp (hρm.div hrm))
  refine Integrable.mono' (hr.const_mul (1 + M ^ 2)) hmeas.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have ha0 : 0 ≤ ρ x / r x := div_nonneg (hρ0 x) (hrp x).le
  have haM : ρ x / r x ≤ M := (div_le_iff₀ (hrp x)).2 (hρM x)
  have hb := t012_abs_mul_log_le ha0 haM
  have heq : ρ x * Real.log (ρ x / r x) = r x * ((ρ x / r x) * Real.log (ρ x / r x)) := by
    have hne : r x ≠ 0 := (hrp x).ne'
    have h : r x * (ρ x / r x) = ρ x := by field_simp
    rw [← mul_assoc, h]
  rw [Real.norm_eq_abs, heq, abs_mul, abs_of_pos (hrp x)]
  calc r x * |ρ x / r x * Real.log (ρ x / r x)| ≤ r x * (1 + M ^ 2) :=
        mul_le_mul_of_nonneg_left hb (hrp x).le
    _ = (1 + M ^ 2) * r x := by ring

/-! ### Gaussian facts -/

theorem t012_integrable_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Euc d => Real.exp (-b * ‖z‖ ^ 2)) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (b : ℂ))
    (by simpa using hb) 0 0
  refine (this.norm).congr (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [Complex.norm_exp]
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem t012_integral_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    ∫ z : Euc d, Real.exp (-b * ‖z‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp

/-- `‖z‖² e^{-b‖z‖²}` is integrable. -/
theorem t012_integrable_sq_mul_exp {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Euc d => ‖z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have h1 := (t012_integrable_exp_neg_sq (d := d) (b := b / 2) (by positivity)).const_mul (2 / b)
  refine Integrable.mono' h1 (by fun_prop : Continuous fun z : Euc d =>
    ‖z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hu := Real.add_one_le_exp (b / 2 * ‖z‖ ^ 2)
  have he : Real.exp (-b * ‖z‖ ^ 2) = Real.exp (-(b / 2) * ‖z‖ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (-(b / 2) * ‖z‖ ^ 2)
  have hinv : Real.exp (b / 2 * ‖z‖ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : b / 2 * ‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2) ≤ 1 := by
    calc b / 2 * ‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2)
        ≤ Real.exp (b / 2 * ‖z‖ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
      _ = 1 := hinv
  rw [he]
  have : ‖z‖ ^ 2 * (Real.exp (-(b / 2) * ‖z‖ ^ 2) * Real.exp (-(b / 2) * ‖z‖ ^ 2))
      = (2 / b) * (b / 2 * ‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2)) * Real.exp (-(b / 2) * ‖z‖ ^ 2) := by
    field_simp
  rw [this]
  have h3 : (2 / b) * (b / 2 * ‖z‖ ^ 2 * Real.exp (-(b / 2) * ‖z‖ ^ 2)) ≤ 2 / b := by
    have : 0 < 2 / b := by positivity
    calc _ ≤ (2 / b) * 1 := mul_le_mul_of_nonneg_left h2 this.le
      _ = 2 / b := by ring
  calc _ ≤ (2 / b) * Real.exp (-(b / 2) * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h3 hpos.le
    _ = _ := by ring

theorem gaussianComparison_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    0 < gaussianComparison d a β x := by
  unfold gaussianComparison
  have : 0 < β * a / (2 * Real.pi) := by positivity
  positivity

theorem gaussianComparison_measurable (a β : ℝ) : Measurable (gaussianComparison d a β) := by
  unfold gaussianComparison
  fun_prop

theorem gaussianComparison_eq (a β : ℝ) (x : Euc d) :
    gaussianComparison d a β x =
      (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
  unfold gaussianComparison
  congr 2; ring

theorem gaussianComparison_integrable {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable (gaussianComparison d a β) := by
  have h := (t012_integrable_exp_neg_sq (d := d) (b := β * a / 2) (by positivity)).const_mul
    ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [gaussianComparison_eq]

/-- `γ = (βa/2π)^{d/2} e^{-βa|x|²/2}` is a probability density. -/
theorem gaussianComparison_isProbDensity {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsProbDensity (gaussianComparison d a β) where
  nonneg x := (gaussianComparison_pos ha hβ x).le
  measurable := gaussianComparison_measurable a β
  integral_one := by
    simp only [gaussianComparison_eq]
    rw [integral_const_mul, t012_integral_exp_neg_sq (by positivity)]
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : β * a / (2 * Real.pi) * (Real.pi / (β * a / 2)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]

theorem gaussianComparison_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    gaussianComparison d a β x ≤ (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by
  rw [gaussianComparison_eq]
  have : Real.exp (-(β * a / 2) * ‖x‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (β * a / 2) * ‖x‖ ^ 2 := by positivity
    linarith
  have hc : 0 < (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by positivity
  calc _ ≤ (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by ring

/-! ### K1 for the Riesz kernel against the Gaussian comparison density -/

theorem t012_rieszK_eq {s : ℝ} (hs : s ≠ 0) (x y : Euc d) :
    rieszKernel d s (x - y) = ‖x - y‖ ^ (-s) := by
  simp [rieszKernel, hs]

theorem t012_rieszK_measurable {s : ℝ} (hs : s ≠ 0) :
    Measurable (Function.uncurry fun x y : Euc d => rieszKernel d s (x - y)) := by
  have : Measurable (rieszKernel d s : Euc d → ℝ) := by
    have h : (rieszKernel d s : Euc d → ℝ) = fun z => ‖z‖ ^ (-s) := funext fun z => by
      simp [rieszKernel, hs]
    rw [h]; exact measurable_norm.pow_const _
  exact this.comp (measurable_fst.sub measurable_snd)

theorem t012_rieszK_nonneg {s : ℝ} (hs : s ≠ 0) (x y : Euc d) : 0 ≤ rieszKernel d s (x - y) := by
  rw [t012_rieszK_eq hs]; exact Real.rpow_nonneg (norm_nonneg _) _

/-- (K1) for `K x y = g (x - y)` and `r = γ`: `g * γ` is bounded and integrable pointwise. -/
theorem riesz_conv_gaussian_bound (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ B : ℝ, ∀ x : Euc d,
      Integrable (fun y => rieszKernel d s (x - y) * gaussianComparison d a β y) ∧
        ∫ y, rieszKernel d s (x - y) * gaussianComparison d a β y ≤ B := by
  have hγ := gaussianComparison_isProbDensity (d := d) ha hβ
  set c : ℝ := (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c * sphereArea d / ((d : ℝ) - s) + 1, fun x => ?_⟩
  have hsa : 0 ≤ sphereArea d := Q34.sphereArea_nonneg hd
  have hds : 0 < (d : ℝ) - s := by linarith
  have hB0 : 0 ≤ c * sphereArea d / ((d : ℝ) - s) + 1 := by positivity
  have hmeasK := t012_rieszK_measurable (d := d) hs0.ne'
  have hm : Measurable fun y => rieszKernel d s (x - y) * gaussianComparison d a β y :=
    (hmeasK.comp (measurable_const.prodMk measurable_id)).mul (gaussianComparison_measurable a β)
  have hlin := Q34.lintegral_kernel_le hd hs0 hsd hγ (M := c) (gaussianComparison_le ha hβ) x
  have hconv : ∫⁻ z, ENNReal.ofReal (‖x - z‖ ^ (-s)) ∂(HRS.Whole.withDensityReal (gaussianComparison d a β)) =
      ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * gaussianComparison d a β y) := by
    rw [Q34.lintegral_nu hγ _ (by
      have : Measurable fun z : Euc d => ‖x - z‖ ^ (-s) :=
        ((measurable_const.sub measurable_id).norm).pow_const _
      exact this.ennreal_ofReal)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (gaussianComparison_pos ha hβ y).le, t012_rieszK_eq hs0.ne', mul_comm]
  rw [hconv] at hlin
  exact t012_int_of_lintegral_le hm
    (fun y => mul_nonneg (t012_rieszK_nonneg hs0.ne' x y) (gaussianComparison_pos ha hβ y).le)
    hB0 hlin

/-! ### Convolution against a density, finite free energy of `ρ ≤ M γ` -/

/-- `g * (ρ dx) (x) = ∫ g(x-y) ρ(y) dy` for a nonnegative measurable density. -/
theorem convMeasure_withDensityReal (g : Euc d → ℝ) {ρ : Euc d → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (x : Euc d) :
    HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) x = ∫ y, g (x - y) * ρ y := by
  unfold HRS.Whole.convMeasure HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y), mul_comm]

/-- Convolution bounds for `0 ≤ ρ ≤ M γ`, `0 < s < d`: the kernel is `ρ dx`-integrable and
`0 ≤ g * ρ ≤ M B` with `B` independent of `ρ` and `M`. -/
theorem convMeasure_bound_of_le (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M : ℝ) (ρ : Euc d → ℝ), HRS.Whole.IsProbDensity ρ → 0 ≤ M →
      (∀ x, ρ x ≤ M * gaussianComparison d a β x) → ∀ x : Euc d,
        Integrable (fun y => rieszKernel d s (x - y)) (HRS.Whole.withDensityReal ρ) ∧
        0 ≤ HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x ∧
        HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x ≤ M * B := by
  obtain ⟨B, hB⟩ := riesz_conv_gaussian_bound (d := d) hd hs0 hsd ha hβ
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun y => mul_nonneg
    (t012_rieszK_nonneg hs0.ne' (0 : Euc d) y) (gaussianComparison_pos ha hβ y).le) (hB 0).2
  refine ⟨B, hB0, fun M ρ hρ hM0 hρM x => ?_⟩
  have hK := t012_rieszK_measurable (d := d) hs0.ne'
  obtain ⟨h1, h2, h3⟩ := conv_bound_of_le hK (t012_rieszK_nonneg hs0.ne') hB hρ.measurable hρ.nonneg
    hM0 hρM x
  refine ⟨?_, ?_, ?_⟩
  · rw [HRS.Whole.withDensityReal, integrable_withDensity_iff_integrable_smul'
      hρ.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg y), mul_comm]
  · rw [convMeasure_withDensityReal _ hρ.measurable hρ.nonneg]; exact h2
  · rw [convMeasure_withDensityReal _ hρ.measurable hρ.nonneg]; exact h3

/-- A probability density `ρ ≤ M γ` has finite free energy (all three Bochner integrals are absolutely
convergent), for `0 < s < d`. -/
theorem hasFiniteFreeEnergy_of_le (hd : 1 ≤ d) {s a β M : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρM : ∀ x, ρ x ≤ M * gaussianComparison d a β x) :
    HRS.Whole.HasFiniteFreeEnergy (rieszKernel d s) (confinement a) ρ := by
  have hM0 : 0 ≤ M := by
    have h := hρM 0
    have := (hρ.nonneg 0).trans h
    have hp := gaussianComparison_pos ha hβ (0 : Euc d)
    by_contra hneg
    have hneg' := not_le.1 hneg
    nlinarith
  have hγi := gaussianComparison_integrable (d := d) ha hβ
  have hγp := gaussianComparison_pos (d := d) ha hβ
  have hγm := gaussianComparison_measurable (d := d) a β
  set c : ℝ := (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hc
  have hcpos : 0 < c := by positivity
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; norm_num)
  -- confinement
  have hVγ : Integrable fun x : Euc d => confinement a x * gaussianComparison d a β x := by
    have h := ((t012_integrable_sq_mul_exp (d := d) (b := β * a / 2) (by positivity)).const_mul
      (a / 2 * c))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [confinement, gaussianComparison_eq, hc]
    ring
  have hVρ : Integrable fun x : Euc d => confinement a x * ρ x := by
    refine Integrable.mono' (hVγ.const_mul M) (by
      have : Measurable fun x : Euc d => confinement a x * ρ x := by
        unfold confinement
        exact (by fun_prop : Measurable fun x : Euc d => a * ‖x‖ ^ 2 / 2).mul hρ.measurable
      exact this.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have hV0 : 0 ≤ confinement a x := by unfold confinement; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hV0 (hρ.nonneg x))]
    calc confinement a x * ρ x ≤ confinement a x * (M * gaussianComparison d a β x) :=
          mul_le_mul_of_nonneg_left (hρM x) hV0
      _ = M * (confinement a x * gaussianComparison d a β x) := by ring
  -- entropy term
  have hlogdiv := t012_integrable_mul_log_div_of_le hγi hγp hγm hρ.measurable hρ.nonneg hρM
  have hpt : ∀ x, ρ x * Real.log (ρ x) =
      ρ x * Real.log (ρ x / gaussianComparison d a β x) + Real.log c * ρ x
        - β * (confinement a x * ρ x) := by
    intro x
    by_cases h0 : ρ x = 0
    · simp [h0]
    · have hlg : Real.log (gaussianComparison d a β x) = Real.log c - β * confinement a x := by
        rw [gaussianComparison_eq, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp]
        unfold confinement; ring
      have hρne : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0)
      rw [Real.log_div hρne.ne' (hγp x).ne', hlg]
      ring
  have hent : Integrable fun x => ρ x * Real.log (ρ x) := by
    have := (hlogdiv.add (hρi.const_mul (Real.log c))).sub (hVρ.const_mul β)
    exact this.congr (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨hent, hVρ, ?_⟩
  obtain ⟨B, hB⟩ := riesz_conv_gaussian_bound (d := d) hd hs0 hsd ha hβ
  have := t012_prod_integrable (t012_rieszK_measurable (d := d) hs0.ne')
    (t012_rieszK_nonneg hs0.ne') (fun y => (gaussianComparison_pos ha hβ y).le) hB
    hρ.measurable hρi hρ.measurable hM0
    (fun y => by rw [abs_of_nonneg (hρ.nonneg y)]; exact hρM y)
  exact this

/-! ### a.e.-invariance -/

theorem convMeasure_congr_ae (g : Euc d → ℝ) {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') (x : Euc d) :
    HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) x = HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ') x := by
  unfold HRS.Whole.convMeasure HRS.Whole.withDensityReal
  rw [withDensity_congr_ae (f := fun y => ENNReal.ofReal (ρ y)) (g := fun y => ENNReal.ofReal (ρ' y))
    (h.mono fun y hy => by simp [hy])]

theorem freeEnergy_congr_ae (g V : Euc d → ℝ) (β : ℝ) {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') :
    HRS.Whole.freeEnergy g V β ρ = HRS.Whole.freeEnergy g V β ρ' := by
  unfold HRS.Whole.freeEnergy
  have h1 : ∫ x, ρ x * Real.log (ρ x) = ∫ x, ρ' x * Real.log (ρ' x) :=
    integral_congr_ae (h.mono fun x hx => by simp [hx])
  have h2 : ∫ x, V x * ρ x = ∫ x, V x * ρ' x :=
    integral_congr_ae (h.mono fun x hx => by simp [hx])
  have h3 : ∫ x, ∫ y, g (x - y) * ρ x * ρ y = ∫ x, ∫ y, g (x - y) * ρ' x * ρ' y := by
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hx, hy]
  rw [h1, h2, h3]

theorem hasFiniteFreeEnergy_congr_ae (g V : Euc d → ℝ) {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') :
    HRS.Whole.HasFiniteFreeEnergy g V ρ ↔ HRS.Whole.HasFiniteFreeEnergy g V ρ' := by
  have key : ∀ {ρ ρ' : Euc d → ℝ}, ρ =ᵐ[volume] ρ' →
      HRS.Whole.HasFiniteFreeEnergy g V ρ → HRS.Whole.HasFiniteFreeEnergy g V ρ' := by
    intro ρ ρ' h ⟨h1, h2, h3⟩
    refine ⟨h1.congr (h.mono fun x hx => by simp [hx]), h2.congr (h.mono fun x hx => by simp [hx]), ?_⟩
    refine h3.congr ?_
    have hf : ρ ∘ Prod.fst =ᵐ[(volume : Measure (Euc d)).prod volume] ρ' ∘ Prod.fst :=
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))).ae_eq_comp h
    have hs : ρ ∘ Prod.snd =ᵐ[(volume : Measure (Euc d)).prod volume] ρ' ∘ Prod.snd :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))).ae_eq_comp h
    filter_upwards [hf, hs] with p hp1 hp2
    simp only [Function.comp] at hp1 hp2
    rw [hp1, hp2]
  exact ⟨key h, key h.symm⟩

end HRS.MS.Thm

end
