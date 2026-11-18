import HRS.MS.Fp81S21GaussSixth

noncomputable section

open MeasureTheory Filter ProbabilityTheory ProbabilityTheory.Fernique
open scoped ENNReal

namespace HRS.Fp81.S21

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- A dimension-free sixth-moment comparison in terms of the second moment. -/
theorem fp81s21_gauss_sixth_lintegral_le {μ : Measure B} [IsProbabilityMeasure μ]
    (hμ : HRS.IsCenteredGaussian μ) :
    ∫⁻ x, ‖x‖ₑ ^ 6 ∂μ ≤
      ENNReal.ofReal (384 / logRatio (3 / 4 : ℝ≥0∞) ^ 3) * HRS.Contr.fernK1 *
        (∫⁻ x, ‖x‖ₑ ^ 2 ∂μ) ^ 3 := by
  set L := logRatio (3 / 4 : ℝ≥0∞) with hL
  have hLpos : 0 < L := HRS.Contr.logRatio_pos'
  set m := ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ with hm
  have hmfin : m < ∞ := by
    have h2 := (HRS.gaussian_sqnorm_integrable hμ).lintegral_lt_top
    rw [hm]
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rcases eq_or_ne m 0 with h0 | h0
  · have hae : ∀ᵐ x ∂μ, ‖x‖ₑ ^ 2 = 0 :=
      (lintegral_eq_zero_iff (by fun_prop)).1 h0
    have : ∫⁻ x, ‖x‖ₑ ^ 6 ∂μ = 0 := by
      refine lintegral_eq_zero_iff (by fun_prop) |>.2 ?_
      filter_upwards [hae] with x hx
      have : ‖x‖ₑ = 0 := by simpa using hx
      simp [this]
    rw [this]; simp
  · have hmpos : 0 < m.toReal := ENNReal.toReal_pos h0 hmfin.ne
    set s := m.toReal with hs
    set a : ℝ := 2 * Real.sqrt s with ha_def
    have ha : 0 < a := by positivity
    have ha2 : a ^ 2 = 4 * s := by
      rw [ha_def, mul_pow, Real.sq_sqrt hmpos.le]; norm_num
    have hms : ENNReal.ofReal s = m := ENNReal.ofReal_toReal hmfin.ne
    have hS : MeasurableSet {x : B | a < ‖x‖} := measurableSet_lt measurable_const measurable_norm
    have hmark : 4 * m * μ {x : B | a < ‖x‖} ≤ m := by
      have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun x : B => ‖x‖ₑ ^ 2)
        (by fun_prop) (4 * m)
      refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) h1
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : (4 * m) = ENNReal.ofReal (a ^ 2) := by
        rw [ha2, ENNReal.ofReal_mul (by norm_num), hms]; norm_num
      rw [this, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le hx.le 2)
    have hcompl : 4 * μ {x : B | a < ‖x‖} ≤ 1 := by
      have : (4 * μ {x : B | a < ‖x‖}) * m ≤ 1 * m := by
        rw [one_mul]; calc _ = 4 * m * μ {x : B | a < ‖x‖} := by ring
          _ ≤ m := hmark
      exact (ENNReal.mul_le_mul_iff_left h0 hmfin.ne).1 this
    have hc : (3 / 4 : ℝ≥0∞) ≤ μ {x : B | ‖x‖ ≤ a} := by
      have e : {x : B | ‖x‖ ≤ a} = {x : B | a < ‖x‖}ᶜ := by
        ext x; simp
      rw [e, prob_compl_eq_one_sub hS]
      refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
      have h4 : (4 : ℝ≥0∞) * (3 / 4 + μ {x : B | a < ‖x‖}) ≤ 4 * 1 := by
        rw [mul_add, mul_one]
        have : (4 : ℝ≥0∞) * (3 / 4) = 3 := by
          rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
        rw [this]
        calc (3 : ℝ≥0∞) + 4 * μ {x : B | a < ‖x‖} ≤ 3 + 1 := by gcongr
          _ = 4 := by norm_num
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h4
    have := hμ.1
    have h_rot := IsGaussian.map_rotation_eq_self (μ := μ)
      (HRS.gaussian_integral_id_eq_zero hμ) (-(Real.pi / 4))
    have hF := lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self (a := a)
      h_rot hc HRS.Contr.three_quarters_gt
    have hF' : ∫⁻ x, ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ ≤ HRS.Contr.fernK1 := hF
    set C : ℝ := 384 / L ^ 3 * s ^ 3 with hC
    have hpt : ∀ x : B, ‖x‖ₑ ^ 6 ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) := by
      intro x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set t : ℝ := L * a⁻¹ ^ 2 with ht
      have htpos : 0 < t := by positivity
      have hy := Real.pow_div_factorial_le_exp (t * ‖x‖ ^ 2) (show 0 ≤ t * ‖x‖ ^ 2 by positivity) 3
      have e1 : C = 6 / t ^ 3 := by
        rw [hC, ht, mul_pow, inv_pow, ha2]
        field_simp
        ring
      rw [e1, show L * a⁻¹ ^ 2 * ‖x‖ ^ 2 = t * ‖x‖ ^ 2 from by rw [ht]]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      norm_num at hy
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg x) 2]
    calc ∫⁻ x, ‖x‖ₑ ^ 6 ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * HRS.Contr.fernK1 := by gcongr
      _ = ENNReal.ofReal (384 / L ^ 3) * HRS.Contr.fernK1 * m ^ 3 := by
          rw [hC, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hmpos.le, hms]
          ring

/-- The quantitative sixth-moment contract with a constant independent of the law. -/
theorem fp81s21_gauss_sixth_bound : fp81s21_GaussSixthStatement (B := B) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (384 / logRatio (3 / 4 : ℝ≥0∞) ^ 3) * HRS.Contr.fernK1
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top HRS.Contr.fernK1_lt_top.ne
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro μ hprob hμ B4 hB4 hi4 hB4bound
  letI : IsProbabilityMeasure μ := hprob
  have hi2 := HRS.gaussian_sqnorm_integrable hμ
  have hi6 := fp81s21_gauss_sixth_integrable μ hμ
  refine ⟨hi6, ?_⟩
  have h2bound : (∫ x : B, ‖x‖ ^ 2 ∂μ) ≤ 1 + B4 := by
    calc
      (∫ x : B, ‖x‖ ^ 2 ∂μ) ≤ ∫ x : B, (1 + ‖x‖ ^ 4) ∂μ := by
        apply integral_mono hi2 ((integrable_const 1).add hi4)
        intro x
        change ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 4
        nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
      _ = 1 + (∫ x : B, ‖x‖ ^ 4 ∂μ) := by
        rw [integral_add (integrable_const 1) hi4]
        simp
      _ ≤ 1 + B4 := by linarith
  have h2nn : 0 ≤ ∫ x : B, ‖x‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => by positivity)
  have h6nn : 0 ≤ ∫ x : B, ‖x‖ ^ 6 ∂μ :=
    integral_nonneg (fun x => by positivity)
  have hconv : ∀ n : ℕ, Integrable (fun x : B => ‖x‖ ^ n) μ →
      (∫⁻ x : B, ‖x‖ₑ ^ n ∂μ) = ENNReal.ofReal (∫ x : B, ‖x‖ ^ n ∂μ) := by
    intro n hn
    rw [ofReal_integral_eq_lintegral_ofReal hn (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hlin := fp81s21_gauss_sixth_lintegral_le hμ
  rw [hconv 6 hi6, hconv 2 hi2] at hlin
  change ENNReal.ofReal (∫ x : B, ‖x‖ ^ 6 ∂μ) ≤
    K * ENNReal.ofReal (∫ x : B, ‖x‖ ^ 2 ∂μ) ^ 3 at hlin
  have hreal := ENNReal.toReal_mono (by finiteness) hlin
  rw [ENNReal.toReal_ofReal h6nn, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal h2nn] at hreal
  have hpow : (1 + B4) ^ 3 ≤ (1 + B4) ^ 6 := by
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  calc
    (∫ x : B, ‖x‖ ^ 6 ∂μ) ≤ K.toReal * (∫ x : B, ‖x‖ ^ 2 ∂μ) ^ 3 := hreal
    _ ≤ K.toReal * (1 + B4) ^ 3 := by gcongr
    _ ≤ K.toReal * (1 + B4) ^ 6 := by gcongr

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_gauss_sixth_lintegral_le
#print axioms HRS.Fp81.S21.fp81s21_gauss_sixth_bound
