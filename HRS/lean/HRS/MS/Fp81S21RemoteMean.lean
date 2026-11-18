import HRS.MS.Fp81S21GaussLaw

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

theorem fp81s21_expected_remote_exp_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ → Ω → ℝ) (M c : ℝ)
    (hb : Measurable (Function.uncurry b))
    (hb0 : ∀ v ω, 0 ≤ b v ω)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hsec : ∀ v, 0 ≤ v →
      Integrable (b v) P ∧ (∫ ω, b v ω ∂P) ≤ M)
    (a L : ℝ) (ha : 0 ≤ a) (hL : 0 < L) :
    Integrable
      (fun ω => ∫ v in Ioc (0 : ℝ) (max (a - L) 0),
        Real.exp (-c * (a - v)) * b v ω ∂volume) P ∧
    (∫ ω, (∫ v in Ioc (0 : ℝ) (max (a - L) 0),
      Real.exp (-c * (a - v)) * b v ω ∂volume) ∂P) ≤
        M * c⁻¹ * Real.exp (-c * L) := by
  let U : ℝ := max (a - L) 0
  let I : Set ℝ := Ioc 0 U
  let μ : Measure ℝ := volume.restrict I
  let w : ℝ → ℝ := fun v => Real.exp (-c * (a - v))
  let f : ℝ × Ω → ℝ := fun z => w z.1 * b z.1 z.2
  have hU : U ≤ a := by
    dsimp [U]
    exact max_le (by linarith) ha
  have hwcont : Continuous w := by
    dsimp [w]
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id))
  have hwint : Integrable w μ := by
    have hI : IntegrableOn w (Ioc 0 U) volume := by
      exact hwcont.integrableOn_Ioc
    simpa [μ, I, IntegrableOn] using hI
  have hfmeas : Measurable f := by
    dsimp [f, w]
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_const.sub measurable_fst))).mul hb
  have hrowMeas : Measurable (fun v => ∫ ω, f (v, ω) ∂P) :=
    (hfmeas.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hrowNonneg (v : ℝ) : 0 ≤ ∫ ω, f (v, ω) ∂P :=
    integral_nonneg fun ω => mul_nonneg (Real.exp_nonneg _) (hb0 v ω)
  have hrowBound (v : ℝ) (hv : v ∈ I) :
      (∫ ω, f (v, ω) ∂P) ≤ M * w v := by
    have hv0 : 0 ≤ v := le_of_lt hv.1
    have hva : v ≤ a := le_trans hv.2 hU
    have hweight : 0 ≤ w v := Real.exp_nonneg _
    have hformula : (∫ ω, f (v, ω) ∂P) = w v * (∫ ω, b v ω ∂P) := by
      simp only [f]
      rw [integral_const_mul]
    rw [hformula]
    calc
      w v * (∫ ω, b v ω ∂P) ≤ w v * M :=
        mul_le_mul_of_nonneg_left (hsec v hv0).2 hweight
      _ = M * w v := by ring
  have hrowBoundAe : ∀ᵐ v ∂μ,
      (∫ ω, f (v, ω) ∂P) ≤ M * w v := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with v hv
    exact hrowBound v (by simpa [I] using hv)
  have hrowValueInt : Integrable (fun v => ∫ ω, f (v, ω) ∂P) μ := by
    refine (hwint.const_mul M).mono' hrowMeas.aestronglyMeasurable ?_
    filter_upwards [hrowBoundAe] with v hv
    rw [Real.norm_of_nonneg (hrowNonneg v)]
    exact hv
  have hsections : ∀ᵐ v ∂μ, Integrable (fun ω => f (v, ω)) P := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with v hv
    have hv0 : 0 ≤ v := le_of_lt (by simpa [I] using hv.1)
    simpa [f] using (hsec v hv0).1.const_mul (w v)
  have hrowNormMeas : Measurable (fun v => ∫ ω, ‖f (v, ω)‖ ∂P) :=
    (hfmeas.norm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hrowNormInt : Integrable (fun v => ∫ ω, ‖f (v, ω)‖ ∂P) μ := by
    refine (hwint.const_mul M).mono' hrowNormMeas.aestronglyMeasurable ?_
    filter_upwards [hrowBoundAe] with v hv
    have heq : (∫ ω, ‖f (v, ω)‖ ∂P) = ∫ ω, f (v, ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hb0 v ω))
    rw [heq, Real.norm_of_nonneg (hrowNonneg v)]
    exact hv
  have hprod : Integrable f (μ.prod P) :=
    (integrable_prod_iff hfmeas.aestronglyMeasurable).2 ⟨hsections, hrowNormInt⟩
  have houterInt : Integrable (fun ω => ∫ v, f (v, ω) ∂μ) P :=
    hprod.integral_prod_right
  have houterInt' : Integrable
      (fun ω => ∫ v in Ioc (0 : ℝ) U, w v * b v ω ∂volume) P := by
    simpa [μ, f, I] using houterInt
  have hbound : (∫ ω, (∫ v in Ioc (0 : ℝ) U, w v * b v ω ∂volume) ∂P) ≤
      M * c⁻¹ * Real.exp (-c * L) := by
    have hswap :
        (∫ ω, (∫ v in Ioc (0 : ℝ) U, w v * b v ω ∂volume) ∂P) =
          ∫ v, (∫ ω, f (v, ω) ∂P) ∂μ := by
      simpa [μ, f, I] using (integral_integral_swap hprod).symm
    rw [hswap]
    calc
      (∫ v, (∫ ω, f (v, ω) ∂P) ∂μ) ≤ ∫ v, M * w v ∂μ :=
        integral_mono_ae hrowValueInt (hwint.const_mul M) hrowBoundAe
      _ = M * (∫ v in Ioc (0 : ℝ) U, w v ∂volume) := by
        rw [integral_const_mul]
      _ ≤ M * (c⁻¹ * Real.exp (-c * L)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        simpa [U, w] using fp81s21_gaussian_remote_exp_integral a L c ha hL hc
      _ = M * c⁻¹ * Real.exp (-c * L) := by ring
  exact ⟨(by simpa [U, w, I] using houterInt'),
    (by simpa [U, w, I] using hbound)⟩

#print axioms fp81s21_expected_remote_exp_bound

end HRS.Fp81.S21

end
