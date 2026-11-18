import HRS.MS.ThmConsAux1

/-!
# C-B (part 2): Gaussian moments of the thermal measure (`0 < s < d`)

From `thermalDensity ≤ C γ` (`cb_thermal_two_sided`) we get `∫ e^{b|x|²} dμ_β < ∞` for `b < βa/2`
(`cb_thermal_exp_moment`) and `∫ |x|^p dμ_β < ∞` for `p ≥ 0` (`cb_thermal_poly_moment`).
-/

open MeasureTheory

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- Integrability against `ρ dx` from integrability of `ρ f` (for a nonnegative measurable `ρ`). -/
lemma cb_integrable_withDensityReal {ρ f : Euc d → ℝ} (hρ : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (h : Integrable (fun x => ρ x * f x)) : Integrable f (HRS.Whole.withDensityReal ρ) := by
  unfold HRS.Whole.withDensityReal
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hn x)]

/-- Gaussian integrability `e^{-c |x|²}`, `c > 0`. -/
lemma cb_integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (c : ℂ))
    (by simpa using hc) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  have : (-(c : ℂ) * (‖x‖ : ℂ) ^ 2) = ((-c * ‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- `e^{b|x|²} γ` is integrable for `b < βa/2`. -/
lemma cb_exp_mul_gauss_integrable {a β b : ℝ} (ha : 0 < a) (hβ : 0 < β) (hb : b < β * a / 2) :
    Integrable (fun x : Euc d => gaussianComparison d a β x * Real.exp (b * ‖x‖ ^ 2)) := by
  have h := (cb_integrable_gauss (d := d) (c := β * a / 2 - b) (by linarith)).const_mul
    ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianComparison, mul_assoc, ← Real.exp_add]
  congr 2
  ring_nf

/-- Gaussian exponential moments of `μ_β` for `b < βa/2`. -/
theorem cb_thermal_exp_moment (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) {b : ℝ} (hb : b < β * a / 2) :
    Integrable (fun x : Euc d => Real.exp (b * ‖x‖ ^ 2)) (thermalMeasure d s a β) := by
  obtain ⟨hP, c, C, hc, hC, hcC⟩ := cb_thermal_two_sided hd hs0 hsd ha hβ
  unfold thermalMeasure
  refine cb_integrable_withDensityReal hP.measurable hP.nonneg ?_
  refine ((cb_exp_mul_gauss_integrable (d := d) ha hβ hb).const_mul C).mono' ?_ ?_
  · exact (hP.measurable.mul (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (hcC x).2
    have h2 := Real.exp_pos (b * ‖x‖ ^ 2)
    rw [Real.norm_of_nonneg (mul_nonneg (hP.nonneg x) h2.le)]
    calc thermalDensity d s a β x * Real.exp (b * ‖x‖ ^ 2)
        ≤ (C * gaussianComparison d a β x) * Real.exp (b * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = C * (gaussianComparison d a β x * Real.exp (b * ‖x‖ ^ 2)) := mul_assoc _ _ _

/-- `y^p ≤ C e^{b y²}` for `y ≥ 0`, `p ≥ 0`, `b > 0`. -/
lemma cb_rpow_le_exp {p b : ℝ} (hp : 0 ≤ p) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 ≤ y → y ^ p ≤ C * Real.exp (b * y ^ 2) := by
  obtain ⟨n, hn⟩ := exists_nat_ge p
  refine ⟨1 + (n.factorial : ℝ) / b ^ n, by positivity, fun y hy => ?_⟩
  have hE1 : 1 ≤ Real.exp (b * y ^ 2) := Real.one_le_exp (by positivity)
  have hpow : (b * y ^ 2) ^ n / n.factorial ≤ Real.exp (b * y ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hbn : 0 < b ^ n := by positivity
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hyn : y ^ (2 * n) ≤ (n.factorial : ℝ) / b ^ n * Real.exp (b * y ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hbn]
    have : (b * y ^ 2) ^ n = b ^ n * y ^ (2 * n) := by rw [mul_pow, ← pow_mul]
    rw [this] at hpow
    rw [div_le_iff₀ hfac] at hpow
    nlinarith [hpow]
  have hy1 : y ^ p ≤ 1 + y ^ (2 * n) := by
    rcases le_total y 1 with h | h
    · have : y ^ p ≤ 1 := Real.rpow_le_one hy h hp
      have : (0 : ℝ) ≤ y ^ (2 * n) := by positivity
      linarith
    · have h1 : y ^ p ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h hn
      rw [Real.rpow_natCast] at h1
      have h2 : y ^ n ≤ y ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  calc y ^ p ≤ 1 + y ^ (2 * n) := hy1
    _ ≤ 1 * Real.exp (b * y ^ 2) + (n.factorial : ℝ) / b ^ n * Real.exp (b * y ^ 2) := by
        linarith
    _ = (1 + (n.factorial : ℝ) / b ^ n) * Real.exp (b * y ^ 2) := by ring

/-- Polynomial moments of `μ_β`. -/
theorem cb_thermal_poly_moment (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x : Euc d => ‖x‖ ^ p) (thermalMeasure d s a β) := by
  have hb : 0 < β * a / 4 := by positivity
  obtain ⟨C, hC, hCb⟩ := cb_rpow_le_exp hp hb
  have hI := (cb_thermal_exp_moment hd hs0 hsd ha hβ (b := β * a / 4) (by nlinarith [mul_pos hβ ha])).const_mul C
  refine hI.mono' ((measurable_norm.pow_const p).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) p)]
  exact hCb ‖x‖ (norm_nonneg x)

end HRS.MS.Thm

end
