import HRS.MS.Fp81S21WindowSup49

/-! Product integrability from uniform scalar sixth-moment slices. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21

/-- Uniform sixth moments on probability-space sections imply integrability on a
finite product. The proof first integrates the sixth power by Tonelli, then uses
`‖x‖ ≤ 1 + ‖x‖^6` and finiteness of the product measure. -/
theorem fp81s21_integrable_of_uniform_sixth
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsFiniteMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : S × Ω → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M)
    (hSix : ∀ s, SixthBound P (fun ω => F (s, ω)) M) :
    Integrable F (μ.prod P) := by
  let G : S × Ω → ℝ := fun z => F z ^ 6
  have hG : Measurable G := hF.pow_const 6
  have hGsection : ∀ s, Integrable (fun ω => G (s, ω)) P := by
    intro s
    have hEq : (fun ω => G (s, ω)) = (fun ω => ‖F (s, ω)‖ ^ 6) := by
      funext ω
      dsimp [G]
      rw [← abs_of_nonneg (by positivity : 0 ≤ F (s, ω) ^ 6)]
      exact abs_pow _ _
    rw [hEq]
    exact (hSix s).1
  let J : S → ℝ := fun s => ∫ ω, ‖G (s, ω)‖ ∂P
  have hJsm : StronglyMeasurable J := hG.stronglyMeasurable.norm.integral_prod_right'
  have hJnonneg : ∀ s, 0 ≤ J s := by
    intro s
    exact integral_nonneg (fun ω => norm_nonneg (G (s, ω)))
  have hJbound : ∀ s, ‖J s‖ ≤ M := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hJnonneg s)]
    calc
      J s = ∫ ω, ‖F (s, ω)‖ ^ 6 ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [J, G]
        exact abs_pow _ _
      _ ≤ M := (hSix s).2
  have hJint : Integrable J μ := by
    refine Integrable.mono' (integrable_const M) hJsm.aestronglyMeasurable ?_
    filter_upwards with s
    simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hJbound s
  have hGprod : Integrable G (μ.prod P) :=
    (integrable_prod_iff hG.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hGsection, hJint⟩
  have hGnorm : Integrable (fun z : S × Ω => ‖F z‖ ^ 6) (μ.prod P) := by
    convert hGprod.norm using 1
    funext z
    dsimp [G]
    exact (abs_pow _ _).symm
  have hMajor : Integrable (fun z : S × Ω => 1 + ‖F z‖ ^ 6) (μ.prod P) :=
    (integrable_const (1 : ℝ)).add hGnorm
  refine Integrable.mono' hMajor hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have hle : ‖F z‖ ≤ 1 + ‖F z‖ ^ 6 := by
    by_cases hx : ‖F z‖ ≤ 1
    · have hpow : 0 ≤ ‖F z‖ ^ 6 := by positivity
      linarith
    · have hx' : 1 ≤ ‖F z‖ := le_of_not_ge hx
      have hpow : 1 ≤ ‖F z‖ ^ 5 := one_le_pow₀ hx'
      calc
        ‖F z‖ = ‖F z‖ * 1 := by ring
        _ ≤ ‖F z‖ * ‖F z‖ ^ 5 := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = ‖F z‖ ^ 6 := by rw [pow_succ]; ring
        _ ≤ 1 + ‖F z‖ ^ 6 := by linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + ‖F z‖ ^ 6)] using hle

/-- Jointly measurable fields with uniform sixth-moment bounds are integrable
on their time products, and Fubini gives one event where both sections are
integrable. -/
theorem fp81s21_joint_source_sixth_integrable
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [IsFiniteMeasure ν]
    (q : S → Ω → ℝ) (k : S × S → Ω → ℝ)
    (hq : Measurable (Function.uncurry q))
    (hk : Measurable (Function.uncurry k))
    (Mq Mk : ℝ) (hMq : 0 ≤ Mq) (hMk : 0 ≤ Mk)
    (hqSix : ∀ s, SixthBound P (q s) Mq)
    (hkSix : ∀ st, SixthBound P (k st) Mk) :
    Integrable (Function.uncurry q) (ν.prod P) ∧
    Integrable (Function.uncurry k) ((ν.prod ν).prod P) ∧
    ∀ᵐ ω ∂P,
      Integrable (fun s => q s ω) ν ∧
      Integrable (fun st => k st ω) (ν.prod ν) := by
  have hqProd := fp81s21_integrable_of_uniform_sixth ν P (Function.uncurry q) hq Mq hMq hqSix
  have hkProd := fp81s21_integrable_of_uniform_sixth (ν.prod ν) P (Function.uncurry k) hk Mk hMk hkSix
  have hqSection : ∀ᵐ ω ∂P, Integrable (fun s => q s ω) ν := by
    have h := hqProd.swap.prod_right_ae
    simpa [Function.comp_def] using h
  have hkSection : ∀ᵐ ω ∂P, Integrable (fun st => k st ω) (ν.prod ν) := by
    have h := hkProd.swap.prod_right_ae
    simpa [Function.comp_def] using h
  refine ⟨hqProd, hkProd, ?_⟩
  filter_upwards [hqSection, hkSection] with ω hqω hkω
  exact ⟨hqω, hkω⟩

#print axioms fp81s21_integrable_of_uniform_sixth
#print axioms fp81s21_joint_source_sixth_integrable
end HRS.Fp81.S21
end
