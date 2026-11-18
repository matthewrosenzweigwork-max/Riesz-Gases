import Mathlib

/-!
# S8L: the standard Gaussian density, its derivative and Stein's lemma (S8.7, block L, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  On a finite-dimensional real inner product space `V`:
the density `s8p_gd (x) = (2π)^{-d/2} e^{-‖x‖²/2}`, its integral `1`, its derivative `-⟪x,·⟫ s8p_gd`, the integrability of
`‖x‖ s8p_gd` and `‖x‖² s8p_gd`, and Gaussian integration by parts `s8p_stein`.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The standard Gaussian density on `V`. -/
def s8p_gd (x : V) : ℝ :=
  (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)

theorem s8p_gd_pos (x : V) : 0 < s8p_gd x := by
  unfold s8p_gd; positivity

theorem s8p_gd_continuous : Continuous (s8p_gd (V := V)) := by
  unfold s8p_gd; fun_prop

theorem s8p_integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (b : ℂ)) (by simpa using hb) 0 0
  have h2 := h.norm
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero]
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, ← Complex.ofReal_pow]

theorem s8p_gd_integrable : Integrable (s8p_gd (V := V)) := by
  unfold s8p_gd
  have := (s8p_integrable_exp_neg_mul_sq_norm (V := V) (b := 1 / 2) (by norm_num)).const_mul
    ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 2; ring

theorem s8p_gd_integral : ∫ x : V, s8p_gd x = 1 := by
  unfold s8p_gd
  rw [integral_const_mul]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := 1 / 2) (by norm_num)
  have e : ∀ x : V, Real.exp (-‖x‖ ^ 2 / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) := fun x => by
    congr 1; ring
  simp_rw [e]
  rw [h]
  have : π / (1 / 2) = 2 * π := by field_simp
  rw [this, ← Real.rpow_add (by positivity)]
  have : -(Module.finrank ℝ V : ℝ) / 2 + (Module.finrank ℝ V : ℝ) / 2 = 0 := by ring
  rw [this]; simp


theorem s8p_gd_hasFDerivAt (x : V) :
    HasFDerivAt (s8p_gd (V := V)) ((-s8p_gd x) • (innerSL ℝ x)) x := by
  have h1 : HasFDerivAt (fun x : V => -(1 / 2 : ℝ) * ‖x‖ ^ 2) (-(1 / 2 : ℝ) • (2 • innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / 2 : ℝ))
  have h2 := (h1.exp).const_mul ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2))
  have e : (s8p_gd (V := V)) = fun y => (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
      Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2) := by
    funext y; unfold s8p_gd; congr 2; ring
  rw [e]
  convert h2 using 1
  ext v
  simp [s8p_gd]
  ring_nf

theorem s8p_gd_fderiv_apply (x v : V) : fderiv ℝ (s8p_gd (V := V)) x v = -(s8p_gd x) * inner ℝ x v := by
  rw [(s8p_gd_hasFDerivAt x).fderiv]; simp

theorem s8p_gd_differentiable : Differentiable ℝ (s8p_gd (V := V)) := fun x =>
  (s8p_gd_hasFDerivAt x).differentiableAt

theorem s8p_gd_mul_norm_sq_le (x : V) :
    ‖x‖ ^ 2 * s8p_gd x ≤ 4 * ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := by
  unfold s8p_gd
  have h1 : ‖x‖ ^ 2 / 4 ≤ Real.exp (‖x‖ ^ 2 / 4) := by
    have := Real.add_one_le_exp (‖x‖ ^ 2 / 4); linarith
  have h3 : ‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) ≤ 4 * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
    have e : Real.exp (-‖x‖ ^ 2 / 2) = (Real.exp (‖x‖ ^ 2 / 4))⁻¹ * Real.exp (-(1/4) * ‖x‖ ^ 2) := by
      rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
    rw [e]
    have hp := Real.exp_pos (‖x‖ ^ 2 / 4)
    have : ‖x‖ ^ 2 * (Real.exp (‖x‖ ^ 2 / 4))⁻¹ ≤ 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith
    calc ‖x‖ ^ 2 * ((Real.exp (‖x‖ ^ 2 / 4))⁻¹ * Real.exp (-(1/4) * ‖x‖ ^ 2))
        = (‖x‖ ^ 2 * (Real.exp (‖x‖ ^ 2 / 4))⁻¹) * Real.exp (-(1/4) * ‖x‖ ^ 2) := by ring
      _ ≤ 4 * Real.exp (-(1 / 4) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hc : 0 ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) := by positivity
  calc ‖x‖ ^ 2 * ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
      = (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * (‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) := by ring
    _ ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * (4 * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hc
    _ = _ := by ring

theorem s8p_gd_mul_norm_sq_integrable : Integrable (fun x : V => ‖x‖ ^ 2 * s8p_gd x) := by
  refine Integrable.mono' (((s8p_integrable_exp_neg_mul_sq_norm (V := V) (b := 1 / 4) (by norm_num)).const_mul
    ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2))).const_mul 4) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_norm.pow 2).mul s8p_gd_continuous).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (s8p_gd_pos x).le)]
    exact s8p_gd_mul_norm_sq_le x

theorem s8p_gd_mul_norm_integrable : Integrable (fun x : V => ‖x‖ * s8p_gd x) := by
  refine Integrable.mono' (s8p_gd_integrable.add s8p_gd_mul_norm_sq_integrable) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact (continuous_norm.mul s8p_gd_continuous).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (s8p_gd_pos x).le)]
    have : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1/2)]
    have hg := s8p_gd_pos x
    simp only [Pi.add_apply]
    nlinarith

/-- Gaussian integration by parts (Stein's lemma). -/
theorem s8p_stein {h : V → ℝ} (hd : Differentiable ℝ h) (v : V)
    (h1 : Integrable (fun x => h x * inner ℝ x v * s8p_gd x))
    (h2 : Integrable (fun x => fderiv ℝ h x v * s8p_gd x))
    (h3 : Integrable (fun x => h x * s8p_gd x)) :
    ∫ x, h x * inner ℝ x v * s8p_gd x = ∫ x, fderiv ℝ h x v * s8p_gd x := by
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure V))
    (f := h) (g := s8p_gd) (v := v)
    h2 (by
      refine h1.neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [s8p_gd_fderiv_apply, Pi.neg_apply]; ring) h3
    (fun x _ => hd x) (fun x _ => s8p_gd_differentiable x)
  simp only [s8p_gd_fderiv_apply] at this
  have e : ∀ x, h x * (-(s8p_gd x) * inner ℝ x v) = -(h x * inner ℝ x v * s8p_gd x) := fun x => by ring
  simp_rw [e, integral_neg] at this
  linarith

end HRS.MS.Spec
