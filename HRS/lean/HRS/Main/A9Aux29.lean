import HRS.Main.A9Aux28

/-!
# Packet A9, part 29: finite-dimensional marginals converge (Lévy), from `d_{C²}`-closeness

`a9_abs_int_sub_le`: a scaled test function in the `C_b²` unit ball is controlled by `smoothDist 2`;
`a9_tendsto_of_ball`: such a (bounded continuous) test function has convergent integrals along `μ_n`
whenever `λ_n → λ_∞` in law and `smoothDist 2 μ_n λ_n → 0`;
`a9_fd_converges`: for a continuous linear map `T : H → ℝ^q`, the marginals `μ_n ∘ T⁻¹` converge weakly
to `λ_∞ ∘ T⁻¹` (Lévy's continuity theorem for the characteristic functions `cos ∘ ℓ, sin ∘ ℓ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace BoundedContinuousFunction

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.Main

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem a9_abs_int_sub_le {f : H → ℝ} {c : ℝ} (hc : 0 < c)
    (hmem : (fun z => c * f z) ∈ CbUnitBall H 2) (μ lam : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure lam] :
    |∫ z, f z ∂μ - ∫ z, f z ∂lam| ≤ smoothDist 2 μ lam / c := by
  have h := abs_integral_sub_le_smoothDist hmem μ lam
  rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos hc] at h
  rw [le_div_iff₀ hc, mul_comm]
  exact h

theorem a9_tendsto_of_ball {f : H → ℝ} (hf : Continuous f) (hb : ∀ z, |f z| ≤ 1) {c : ℝ}
    (hc : 0 < c) (hmem : (fun z => c * f z) ∈ CbUnitBall H 2)
    (μ lam : ℕ → Measure H) (lam₀ : Measure H) [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (lam n)] [IsProbabilityMeasure lam₀]
    (hlc : ConvergesInLaw lam lam₀)
    (hd : Tendsto (fun n => smoothDist 2 (μ n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, f z ∂(μ n)) atTop (𝓝 (∫ z, f z ∂lam₀)) := by
  let F : H →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ 2 (fun x y => by
    show dist (f x) (f y) ≤ 2
    rw [Real.dist_eq]
    have h1 := abs_le.1 (hb x)
    have h2 := abs_le.1 (hb y)
    rw [abs_le]; constructor <;> linarith)
  have h1 : Tendsto (fun n => ∫ z, f z ∂(lam n)) atTop (𝓝 (∫ z, f z ∂lam₀)) := hlc F
  have h2 : Tendsto (fun n => ∫ z, f z ∂(μ n) - ∫ z, f z ∂(lam n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hd.div_const c)
    rw [Real.norm_eq_abs]
    exact a9_abs_int_sub_le hc hmem (μ n) (lam n)
  have := h2.add h1
  simpa using this

theorem a9_int_cexp (μ : Measure H) [IsProbabilityMeasure μ] (f : H → ℝ) (hf : Measurable f) :
    ∫ x, Complex.exp (((f x : ℝ) : ℂ) * Complex.I) ∂μ =
      ((∫ x, Real.cos (f x) ∂μ : ℝ) : ℂ) + ((∫ x, Real.sin (f x) ∂μ : ℝ) : ℂ) * Complex.I := by
  have e : ∀ x, Complex.exp (((f x : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (f x) : ℝ) : ℂ) + ((Real.sin (f x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hc : Integrable (fun x => Real.cos (f x)) μ :=
    Integrable.of_bound (Real.continuous_cos.measurable.comp hf).aestronglyMeasurable 1
      (ae_of_all _ fun x => by simpa using Real.abs_cos_le_one _)
  have hs : Integrable (fun x => Real.sin (f x)) μ :=
    Integrable.of_bound (Real.continuous_sin.measurable.comp hf).aestronglyMeasurable 1
      (ae_of_all _ fun x => by simpa using Real.abs_sin_le_one _)
  simp_rw [e]
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_complex_ofReal, integral_mul_const,
    integral_complex_ofReal]

theorem a9_fd_converges {q : ℕ} (T : H →L[ℝ] ℝ^q)
    (μ lam : ℕ → Measure H) (lam₀ : Measure H) [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (lam n)] [IsProbabilityMeasure lam₀]
    (hlc : ConvergesInLaw lam lam₀)
    (hd : Tendsto (fun n => smoothDist 2 (μ n) (lam n)) atTop (𝓝 0))
    (g : (ℝ^q) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g (T x) ∂(μ n)) atTop (𝓝 (∫ x, g (T x) ∂lam₀)) := by
  have hTm : Measurable T := T.continuous.measurable
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map T) := fun n =>
    inferInstance
  haveI : IsProbabilityMeasure (lam₀.map T) := inferInstance
  let ν : ℕ → ProbabilityMeasure (ℝ^q) := fun n => ⟨(μ n).map T, inferInstance⟩
  let ν₀ : ProbabilityMeasure (ℝ^q) := ⟨lam₀.map T, inferInstance⟩
  have hlev : Tendsto ν atTop (𝓝 ν₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ξ => ?_
    set ℓ : StrongDual ℝ H := (innerSL ℝ ξ).comp T with hℓ
    have hℓa : ∀ x, ℓ x = inner ℝ (T x) ξ := fun x => by
      rw [hℓ]; simp [real_inner_comm]
    have hcf : ∀ (m : Measure H) [IsProbabilityMeasure m],
        charFun (m.map T) ξ = ((∫ x, Real.cos (ℓ x) ∂m : ℝ) : ℂ) +
          ((∫ x, Real.sin (ℓ x) ∂m : ℝ) : ℂ) * Complex.I := by
      intro m _
      rw [charFun_apply, integral_map hTm.aemeasurable]
      · simp_rw [← hℓa]
        exact a9_int_cexp m ℓ ℓ.continuous.measurable
      · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_id.inner continuous_const)).mul continuous_const)).aestronglyMeasurable
    have hM : (0 : ℝ) < 3 * max 1 (‖ℓ‖ ^ 2) :=
      by have := lt_of_lt_of_le one_pos (le_max_left 1 (‖ℓ‖ ^ 2)); positivity
    have hMc : 0 < 1 / (3 * max 1 (‖ℓ‖ ^ 2)) := by positivity
    have tc := a9_tendsto_of_ball (f := fun x => Real.cos (ℓ x))
      (Real.continuous_cos.comp ℓ.continuous) (fun z => Real.abs_cos_le_one _) hMc
      (a9_cos_mem ℓ) μ lam lam₀ hlc hd
    have ts := a9_tendsto_of_ball (f := fun x => Real.sin (ℓ x))
      (Real.continuous_sin.comp ℓ.continuous) (fun z => Real.abs_sin_le_one _) hMc
      (a9_sin_mem ℓ) μ lam lam₀ hlc hd
    have key := ((Complex.continuous_ofReal.tendsto _).comp tc).add
      (((Complex.continuous_ofReal.tendsto _).comp ts).mul_const Complex.I)
    show Tendsto (fun n => charFun ((μ n).map T) ξ) atTop (𝓝 (charFun (lam₀.map T) ξ))
    rw [hcf lam₀]
    exact key.congr (fun n => (hcf (μ n)).symm)
  have h3 : Tendsto (fun n => ∫ y, g y ∂((μ n).map T)) atTop (𝓝 (∫ y, g y ∂(lam₀.map T))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlev g
  have e1 : ∀ m : Measure H, ∫ y, g y ∂(m.map T) = ∫ x, g (T x) ∂m := fun m =>
    integral_map hTm.aemeasurable g.continuous.aestronglyMeasurable
  simpa only [e1] using h3

end HRS.Main.A9
