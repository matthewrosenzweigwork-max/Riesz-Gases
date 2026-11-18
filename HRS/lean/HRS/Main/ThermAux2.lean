import HRS.Main.Headline

/-!
# THERM helper 2: `W_1 → 0` implies weak convergence (`ConvergesInLaw`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

section Weak

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-- Bounded Lipschitz test functions are controlled by `W_1`. -/
theorem therm_lip_integral_le (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : B → ℝ) (L : ℝ≥0) (hL : 0 < L) (hf : LipschitzWith L f) (C : ℝ)
    (hC : ∀ x y, dist (f x) (f y) ≤ C) :
    ENNReal.ofReal |∫ x, f x ∂P - ∫ x, f x ∂Q| ≤ (L : ℝ≥0∞) * wassersteinE 1 P Q := by
  have hfc : Continuous f := hf.continuous
  have hfm : Measurable f := hfc.measurable
  unfold wassersteinE
  rw [ENNReal.mul_iInf_of_ne (by simpa using hL.ne') (by simp)]
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  have hπ : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  have hbd : ∀ z : B × B, |f z.1| ≤ |f 0| + C := fun z => by
    have := hC z.1 0
    rw [Real.dist_eq] at this
    calc |f z.1| = |(f z.1 - f 0) + f 0| := by ring_nf
      _ ≤ |f z.1 - f 0| + |f 0| := abs_add_le _ _
      _ ≤ C + |f 0| := by linarith
      _ = _ := by ring
  have hbd2 : ∀ z : B × B, |f z.2| ≤ |f 0| + C := fun z => by
    have := hC z.2 0
    rw [Real.dist_eq] at this
    calc |f z.2| = |(f z.2 - f 0) + f 0| := by ring_nf
      _ ≤ |f z.2 - f 0| + |f 0| := abs_add_le _ _
      _ ≤ C + |f 0| := by linarith
      _ = _ := by ring
  have i1 : Integrable (fun z : B × B => f z.1) π.1 :=
    Integrable.of_bound (hfm.comp measurable_fst).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun z => by simpa using hbd z)
  have i2 : Integrable (fun z : B × B => f z.2) π.1 :=
    Integrable.of_bound (hfm.comp measurable_snd).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun z => by simpa using hbd2 z)
  have e1 : ∫ x, f x ∂P = ∫ z, f z.1 ∂π.1 := by
    have := integral_map (μ := π.1) measurable_fst.aemeasurable hfc.aestronglyMeasurable
    rw [h1] at this
    exact this
  have e2 : ∫ x, f x ∂Q = ∫ z, f z.2 ∂π.1 := by
    have := integral_map (μ := π.1) measurable_snd.aemeasurable hfc.aestronglyMeasurable
    rw [h2] at this
    exact this
  rw [e1, e2, ← integral_sub i1 i2]
  have hn := enorm_integral_le_lintegral_enorm (μ := π.1) (fun z : B × B => f z.1 - f z.2)
  have hle : ∫⁻ z, ‖f z.1 - f z.2‖ₑ ∂π.1 ≤ (L : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1 := by
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun z => ?_
    have := hf.edist_le_mul z.1 z.2
    rw [edist_eq_enorm_sub, edist_eq_enorm_sub] at this
    simpa [Real.rpow_one, ofReal_norm_eq_enorm] using this
  have hr : ENNReal.ofReal |∫ z, (f z.1 - f z.2) ∂π.1| =
      ‖∫ z, (f z.1 - f z.2) ∂π.1‖ₑ := by
    rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
  rw [hr]
  refine hn.trans (hle.trans ?_)
  simp

/-- `W_1 → 0` for probability measures implies weak convergence. -/
theorem therm_convergesInLaw_of_W1 (μ : ℕ → Measure B) (ν : Measure B) [IsProbabilityMeasure ν]
    (hprob : ∀ᶠ N in atTop, IsProbabilityMeasure (μ N))
    (hW : Tendsto (fun N => wassersteinE 1 (μ N) ν) atTop (𝓝 0)) :
    ConvergesInLaw μ ν := by
  classical
  let μs : ℕ → ProbabilityMeasure B := fun N =>
    if h : IsProbabilityMeasure (μ N) then @Measure.toProbabilityMeasure _ _ (μ N) h else ν.toProbabilityMeasure
  have hμs : ∀ᶠ N in atTop, (μs N : Measure B) = μ N := hprob.mono fun N hN => by
    simp [μs, hN]
  have hT : Tendsto μs atTop (𝓝 ν.toProbabilityMeasure) := by
    rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f ⟨C, hC⟩ ⟨L, hL⟩
    have hL' : LipschitzWith (L + 1) f := hL.weaken (by simp)
    have hpos : 0 < L + 1 := by positivity
    have hb : Tendsto (fun N => ENNReal.ofReal |∫ x, f x ∂(μs N : Measure B) - ∫ x, f x ∂ν|)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun N => ((L + 1 : ℝ≥0) : ℝ≥0∞) * wassersteinE 1 (μ N) ν) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hW (Or.inr (by simp))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [hμs, hprob] with N h1 h2
      rw [h1]
      exact therm_lip_integral_le (μ N) ν f (L + 1) hpos hL' C hC
    have h3 : Tendsto (fun N => |∫ x, f x ∂(μs N : Measure B) - ∫ x, f x ∂ν|) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp hb
      simpa [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using this
    have h4 : Tendsto (fun N => ∫ x, f x ∂(μs N : Measure B) - ∫ x, f x ∂ν) atTop (𝓝 0) := by
      simpa using (tendsto_zero_iff_abs_tendsto_zero _).2 h3
    simpa using h4.add_const (∫ x, f x ∂ν) |>.congr (fun N => by ring)
  have hT' := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT
  intro f
  refine (hT' f).congr' (hμs.mono fun N hN => ?_)
  simp [hN]

end Weak

end Main

end HRS
