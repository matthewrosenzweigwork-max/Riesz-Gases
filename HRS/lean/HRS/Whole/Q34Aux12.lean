import HRS.Whole.Q34Aux11

/-!
# Packet Q34, helper file 12: positive definiteness of the Gaussian kernel
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem gauss_cos (t : Euc d) :
    ∫ ξ, Real.cos (inner ℝ ξ t) ∂(stdGaussian (Euc d)) = Real.exp (-‖t‖ ^ 2 / 2) := by
  have h := charFun_stdGaussian (E := Euc d) t
  rw [charFun_apply] at h
  have h2 := congrArg Complex.re h
  have hint : Integrable (fun ξ : Euc d => Complex.exp (↑(inner ℝ ξ t) * Complex.I))
      (stdGaussian (Euc d)) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Continuous (fun ξ : Euc d =>
        Complex.exp (↑(inner ℝ ξ t) * Complex.I))).aestronglyMeasurable
    · simp [Complex.norm_exp_ofReal_mul_I]
  have h3 := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at h3
  rw [← h3] at h2
  simp only [Complex.exp_ofReal_mul_I_re] at h2
  rw [h2]
  have : (-(‖t‖ : ℂ) ^ 2 / 2) = ((-‖t‖ ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.exp_ofReal_re]

/-- Gaussian kernel as an average of cosines. -/
theorem gauss_kernel_eq {τ : ℝ} (hτ : 0 < τ) (x y : Euc d) :
    Real.exp (-τ * ‖x - y‖ ^ 2) = ∫ ξ, Real.cos (Real.sqrt (2 * τ) *
      (inner ℝ ξ x - inner ℝ ξ y)) ∂(stdGaussian (Euc d)) := by
  have h := gauss_cos (Real.sqrt (2 * τ) • (x - y))
  have e1 : ∀ ξ : Euc d, inner ℝ ξ (Real.sqrt (2 * τ) • (x - y)) =
      Real.sqrt (2 * τ) * (inner ℝ ξ x - inner ℝ ξ y) := by
    intro ξ
    rw [inner_smul_right, inner_sub_right]
  simp only [e1] at h
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]
  congr 1
  ring

/-- The Gaussian kernel `e^{-τ|x-y|²}` is positive definite. -/
theorem gauss_posdef {ν : Measure (Euc d)} [IsFiniteMeasure ν] {u : Euc d → ℝ}
    (hum : Measurable u) (hu : Integrable u ν) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ ∫ z, Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2 ∂(ν.prod ν) := by
  set γ := stdGaussian (Euc d) with hγ
  set l : ℝ := Real.sqrt (2 * τ) with hl
  have hmaj : Integrable (fun z : Euc d × Euc d => |u z.1| * |u z.2|) (ν.prod ν) :=
    hu.abs.mul_prod hu.abs
  -- the integrand on the product space is integrable
  have hint1 : Integrable (fun z : Euc d × Euc d =>
      Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2) (ν.prod ν) := by
    refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (((by fun_prop : Measurable (fun z : Euc d × Euc d =>
        Real.exp (-τ * ‖z.1 - z.2‖ ^ 2))).mul (hum.comp measurable_fst)).mul
          (hum.comp measurable_snd)).aestronglyMeasurable
    · have h1 : Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖z.1 - z.2‖]
      have h2 : 0 ≤ Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) := (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h2]
      calc Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) * |u z.1| * |u z.2|
          ≤ 1 * |u z.1| * |u z.2| := by gcongr
        _ = |u z.1| * |u z.2| := by ring
  set Φ : (Euc d × Euc d) × Euc d → ℝ := fun p =>
    u p.1.1 * u p.1.2 * Real.cos (l * (inner ℝ p.2 p.1.1 - inner ℝ p.2 p.1.2)) with hΦ
  have hΦm : Measurable Φ := by
    have h1 : Measurable (fun p : (Euc d × Euc d) × Euc d => inner ℝ p.2 p.1.1) :=
      (continuous_snd.inner (continuous_fst.comp continuous_fst)).measurable
    have h2 : Measurable (fun p : (Euc d × Euc d) × Euc d => inner ℝ p.2 p.1.2) :=
      (continuous_snd.inner (continuous_snd.comp continuous_fst)).measurable
    exact (((hum.comp (measurable_fst.comp measurable_fst)).mul
      (hum.comp (measurable_snd.comp measurable_fst))).mul
        (Real.measurable_cos.comp ((h1.sub h2).const_mul l)))
  have hΦi : Integrable Φ ((ν.prod ν).prod γ) := by
    have hmaj2 : Integrable (fun p : (Euc d × Euc d) × Euc d => |u p.1.1| * |u p.1.2|)
        ((ν.prod ν).prod γ) := by
      have := hmaj.mul_prod (integrable_const (1 : ℝ) (μ := γ))
      simpa using this
    refine Integrable.mono' hmaj2 hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [hΦ]
    simp only [Real.norm_eq_abs, abs_mul]
    calc |u p.1.1| * |u p.1.2| * |Real.cos (l * (inner ℝ p.2 p.1.1 - inner ℝ p.2 p.1.2))|
        ≤ |u p.1.1| * |u p.1.2| * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = _ := by ring
  have hstep1 : ∫ z, Real.exp (-τ * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2 ∂(ν.prod ν) =
      ∫ z, ∫ ξ, Φ (z, ξ) ∂γ ∂(ν.prod ν) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hΦ]
    rw [integral_const_mul, ← gauss_kernel_eq hτ]
    ring
  rw [hstep1, integral_integral_swap (f := fun z ξ => Φ (z, ξ)) hΦi]
  refine integral_nonneg fun ξ => ?_
  set f1 : Euc d → ℝ := fun x => u x * Real.cos (l * inner ℝ ξ x) with hf1
  set f2 : Euc d → ℝ := fun x => u x * Real.sin (l * inner ℝ ξ x) with hf2
  have hf1m : Measurable f1 := hum.mul (Real.measurable_cos.comp
    ((continuous_const.inner continuous_id).measurable.const_mul l))
  have hf2m : Measurable f2 := hum.mul (Real.measurable_sin.comp
    ((continuous_const.inner continuous_id).measurable.const_mul l))
  have hf1i : Integrable f1 ν := by
    refine Integrable.mono' hu.abs hf1m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [hf1]; simp only [Real.norm_eq_abs, abs_mul]
    calc |u x| * |Real.cos (l * inner ℝ ξ x)| ≤ |u x| * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = |u x| := by ring
  have hf2i : Integrable f2 ν := by
    refine Integrable.mono' hu.abs hf2m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [hf2]; simp only [Real.norm_eq_abs, abs_mul]
    calc |u x| * |Real.sin (l * inner ℝ ξ x)| ≤ |u x| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |u x| := by ring
  have hsplit : ∀ z : Euc d × Euc d, Φ (z, ξ) = f1 z.1 * f1 z.2 + f2 z.1 * f2 z.2 := by
    intro z
    simp only [hΦ, hf1, hf2]
    rw [mul_sub, Real.cos_sub]
    ring
  simp_rw [hsplit]
  rw [integral_add (hf1i.mul_prod hf1i) (hf2i.mul_prod hf2i), integral_prod_mul, integral_prod_mul]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

end HRS.Whole.Q34
