import HRS.Whole.Q34Aux2

/-!
# Packet Q34, helper file 5: the compensated exponential `e^{-a} - 1 + a`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

/-- The compensated exponential `κ(a) = e^{-a} - 1 + a`. -/
def kk (a : ℝ) : ℝ := Real.exp (-a) - 1 + a

theorem kk_nonneg {a : ℝ} (_ : 0 ≤ a) : 0 ≤ kk a := by
  unfold kk
  have := Real.add_one_le_exp (-a)
  linarith

theorem kk_le_self {a : ℝ} (ha : 0 ≤ a) : kk a ≤ a := by
  unfold kk
  have : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith

/-- Taylor's integral formula for `κ`. -/
theorem integral_taylor {a : ℝ} (ha : 0 < a) :
    ∫ τ in Icc (0 : ℝ) 1, (1 - τ) * Real.exp (-τ * a) = kk a / a ^ 2 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => (-1 / a) * ((1 - t) * Real.exp (-t * a)) + (1 / a ^ 2) * Real.exp (-t * a))
      ((1 - x) * Real.exp (-x * a)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -t * a) (-a) x := by
      simpa using (hasDerivAt_neg x).mul_const a
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t * a)) (Real.exp (-x * a) * (-a)) x :=
      h1.exp
    have h3 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h4 := ((h3.mul h2).const_mul (-1 / a)).add (h2.const_mul (1 / a ^ 2))
    convert h4 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (1 - x) * Real.exp (-x * a)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : Real.exp (-(0 : ℝ) * a) = 1 := by simp
  have h1 : Real.exp (-(1 : ℝ) * a) = Real.exp (-a) := by simp
  simp only [h0, h1, sub_zero, one_mul, mul_one, sub_self, zero_mul]
  unfold kk
  field_simp
  ring

theorem kk_le_half_sq {a : ℝ} (ha : 0 ≤ a) : kk a ≤ a ^ 2 / 2 := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp [kk]
  · have h1 := integral_taylor h
    have h2 : ∫ τ in Icc (0 : ℝ) 1, (1 - τ) * Real.exp (-τ * a) ≤ ∫ τ in Icc (0 : ℝ) 1, (1 - τ) := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · intro τ hτ
        have : Real.exp (-τ * a) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [hτ.1, hτ.2]
        have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
        nlinarith
    have h3 : ∫ τ in Icc (0 : ℝ) 1, (1 - τ) = 1 / 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp
      norm_num
    rw [h1, h3] at h2
    have hp : 0 < a ^ 2 := by positivity
    rw [div_le_iff₀ hp] at h2
    linarith


/-- Substitution `y = t^{-s}` in a nonnegative `lintegral` over `(0,∞)`. -/
theorem lintegral_subst_neg_rpow {s : ℝ} (hs : 0 < s) (α : ℝ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ α) * G y =
      ENNReal.ofReal s * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-s * α - s - 1)) * G (t ^ (-s)) := by
  have himg : (fun t : ℝ => t ^ (-s)) '' (Ioi 0) = Ioi (0 : ℝ) := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact Real.rpow_pos_of_pos hy _
    · exact fun hx => ⟨x ^ (1 / (-s)), Real.rpow_pos_of_pos hx _, by
        simp [← Real.rpow_mul (le_of_lt hx), hs.ne']⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => t ^ (-s)) (f' := fun t => -s * t ^ (-s - 1)) measurableSet_Ioi
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn (by linarith : -s ≠ 0)).mono (by
      intro x hx; exact (mem_Ioi.mp hx).le)) (fun y => ENNReal.ofReal (y ^ α) * G y)
  rw [himg] at key
  rw [key, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have h1 : |(-s * t ^ (-s - 1))| = s * t ^ (-s - 1) := by
    rw [abs_mul, abs_neg, abs_of_pos hs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  simp only [h1]
  have e : s * t ^ (-s - 1) * (t ^ (-s)) ^ α = s * t ^ (-s * α - s - 1) := by
    rw [← Real.rpow_mul ht0.le, mul_assoc, ← Real.rpow_add ht0]
    congr 2; ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), e, ENNReal.ofReal_mul hs.le, mul_assoc]


/-- Step A: `y^{-p-1} κ(y)` as a `lintegral` over `τ ∈ (0,1]`. -/
theorem kk_lintegral_taylor {y : ℝ} (hy : 0 < y) (p : ℝ) :
    ENNReal.ofReal (y ^ (-p - 1)) * ENNReal.ofReal (kk y) =
      ∫⁻ τ in Ioc (0 : ℝ) 1, ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) := by
  have h1 := integral_taylor hy
  rw [integral_Icc_eq_integral_Ioc] at h1
  have hint : IntegrableOn (fun τ : ℝ => y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) (Ioc 0 1) := by
    have : Continuous (fun τ : ℝ => y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) := by fun_prop
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun τ : ℝ => y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have : 0 ≤ 1 - τ := by linarith [hτ.2]
    have := Real.exp_pos (-(τ * y))
    have := Real.rpow_nonneg hy.le (1 - p)
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul]
  have h2 : ∫ τ in Ioc (0 : ℝ) 1, (1 - τ) * Real.exp (-(τ * y)) = kk y / y ^ 2 := by
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
    simp [neg_mul]
  rw [h2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _)]
  congr 1
  have : y ^ (-p - 1) = y ^ (1 - p) / y ^ 2 := by
    rw [← Real.rpow_natCast y 2, ← Real.rpow_sub hy]
    congr 1; push_cast; ring
  rw [this]
  ring

/-- Step C: the Gamma integral in `lintegral` form. -/
theorem lintegral_gamma_aux {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(τ * y))) =
      ENNReal.ofReal ((1 / τ) ^ a * Real.Gamma a) := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi ha hτ]
  have hint : IntegrableOn (fun y : ℝ => y ^ (a - 1) * Real.exp (-(τ * y))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := τ)
      (by linarith) one_pos hτ
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have := Real.exp_pos (-(τ * y))
  have := Real.rpow_nonneg (le_of_lt (mem_Ioi.mp hy)) (a - 1)
  positivity


/-- The `v`-integral `∫₀^∞ (e^{-v} - 1 + v) v^{-p-1} dv = Γ(2-p)/(p(p-1))`, `1 < p < 2`. -/
theorem lintegral_kk_mass {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (-p - 1)) * ENNReal.ofReal (kk y) =
      ENNReal.ofReal (Real.Gamma (2 - p) / (p * (p - 1))) := by
  have hΓ : 0 < Real.Gamma (2 - p) := Real.Gamma_pos_of_pos (by linarith)
  have step1 : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (-p - 1)) * ENNReal.ofReal (kk y) =
      ∫⁻ y in Ioi (0 : ℝ), ∫⁻ τ in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    exact kk_lintegral_taylor (mem_Ioi.mp hy) p
  have hmeas : Measurable (Function.uncurry fun (y τ : ℝ) =>
      ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y))))) := by
    apply Measurable.ennreal_ofReal
    fun_prop
  have step2 := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun (y τ : ℝ) => ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))))
    hmeas.aemeasurable
  have step3 : ∀ τ ∈ Ioc (0 : ℝ) 1,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) =
        ENNReal.ofReal ((1 - τ) * (τ ^ (p - 2) * Real.Gamma (2 - p))) := by
    intro τ hτ
    have hτ0 : 0 < τ := hτ.1
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    have e1 : ∀ y ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (y ^ (1 - p) * ((1 - τ) * Real.exp (-(τ * y)))) =
        ENNReal.ofReal (1 - τ) * ENNReal.ofReal (y ^ ((2 - p) - 1) * Real.exp (-(τ * y))) := by
      intro y _
      rw [← ENNReal.ofReal_mul h1τ]
      congr 1
      have : (2 - p) - 1 = 1 - p := by ring
      rw [this]; ring
    rw [setLIntegral_congr_fun measurableSet_Ioi e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_gamma_aux (by linarith : 0 < 2 - p) hτ0, ← ENNReal.ofReal_mul h1τ]
    congr 2
    rw [one_div, Real.inv_rpow hτ0.le, ← Real.rpow_neg hτ0.le]
    congr 2; ring
  have step4 : ∫⁻ τ in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - τ) * (τ ^ (p - 2) * Real.Gamma (2 - p))) =
      ENNReal.ofReal (Real.Gamma (2 - p) / (p * (p - 1))) := by
    have hi1 : IntegrableOn (fun τ : ℝ => τ ^ (p - 2)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hi2 : IntegrableOn (fun τ : ℝ => τ ^ (p - 1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hform : ∀ τ ∈ Ioc (0 : ℝ) 1, (1 - τ) * (τ ^ (p - 2) * Real.Gamma (2 - p)) =
        Real.Gamma (2 - p) * (τ ^ (p - 2) - τ ^ (p - 1)) := by
      intro τ hτ
      have hτ0 : 0 < τ := hτ.1
      have : τ ^ (p - 1) = τ ^ (p - 2) * τ := by
        rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hτ0, Real.rpow_one]
      rw [this]; ring
    have hint : IntegrableOn (fun τ : ℝ => (1 - τ) * (τ ^ (p - 2) * Real.Gamma (2 - p)))
        (Ioc 0 1) := by
      refine IntegrableOn.congr_fun ((hi1.sub hi2).const_mul (Real.Gamma (2 - p))) ?_
        measurableSet_Ioc
      intro τ hτ; exact (hform τ hτ).symm
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        (fun τ : ℝ => (1 - τ) * (τ ^ (p - 2) * Real.Gamma (2 - p))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
      have : 0 ≤ 1 - τ := by linarith [hτ.2]
      have := Real.rpow_nonneg hτ.1.le (p - 2)
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioc hform, integral_const_mul,
      integral_sub hi1 hi2]
    have hI1 : ∫ τ in Ioc (0 : ℝ) 1, τ ^ (p - 2) = 1 / (p - 1) := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
      rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (by linarith)]
      simp
    have hI2 : ∫ τ in Ioc (0 : ℝ) 1, τ ^ (p - 1) = 1 / p := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
      rw [show p - 1 + 1 = p by ring, Real.zero_rpow (by linarith)]
      simp
    rw [hI1, hI2]
    have : p - 1 ≠ 0 := by linarith
    have : p ≠ 0 := by linarith
    field_simp
    ring
  rw [step1, step2, ← step4]
  refine setLIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
  exact step3 τ hτ

end HRS.Whole.Q34
