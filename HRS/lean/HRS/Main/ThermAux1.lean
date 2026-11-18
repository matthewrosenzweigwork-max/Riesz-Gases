import HRS.Main.Headline
import HRS.Sections.IIDFinal

/-!
# THERM helper 1: the mixture preparation (Example 2.6), marginal and density identification

Helpers are prefixed `therm_` and live in `HRS.Main`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- A smooth function on the torus is continuous. -/
theorem therm_continuous_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).continuous

/-- `(ρ dx).withDensity (ofReal f) = (f ρ) dx` for a nonnegative measurable density `ρ`. -/
theorem therm_withDensity_eq {ρ f : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Measurable ρ)
    (hf : Measurable f) :
    (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (f x)) =
      withDensityReal (fun x => f x * ρ x) := by
  unfold withDensityReal
  have h := withDensity_mul (volume : Measure (Torus d))
    (f := fun x => ENNReal.ofReal (ρ x)) (g := fun x => ENNReal.ofReal (f x))
    (ENNReal.measurable_ofReal.comp hρ) (ENNReal.measurable_ofReal.comp hf)
  refine Eq.trans h.symm ?_
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul' (hρ0 x), mul_comm]

/-- `mixturePrep` is the mixture of the two density-modified products of `withDensityReal`. -/
theorem therm_mixturePrep_eq (S : PreparedData d) (b : Torus d → ℝ) (hb : Measurable b) (a₀ : ℝ)
    (N : ℕ) :
    mixturePrep S.μ0 b a₀ N =
      (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
          withDensityReal fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x) +
        (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
          withDensityReal fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x) := by
  have h0 := S.hρ0.density.nonneg
  have hm := S.hρ0.density.measurable
  unfold mixturePrep PreparedData.μ0
  rw [therm_withDensity_eq h0 hm (by fun_prop), therm_withDensity_eq h0 hm (by fun_prop)]
  simp only [one_div]

/-- The density `(1 + κ b) ρ°` is a probability density when it is positive and `μ°(b) = 0`. -/
theorem therm_mixDensity_prob (S : PreparedData d) {b : Torus d → ℝ} (hb : Torus.IsSmooth b)
    (hb0 : pair S.μ0 b = 0) (κ : ℝ) (hκ : ∀ x, 0 < 1 + κ * b x) :
    IsProbDensity (fun x => (1 + κ * b x) * S.ρ0 x) := by
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hρc : Continuous S.ρ0 := therm_continuous_of_smooth S.hρ0.smooth
  have h0 := S.hρ0.density.nonneg
  have hm := S.hρ0.density.measurable
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hbρ : ∫ x, b x * S.ρ0 x = 0 := by
    have := HRS.integral_withDensityReal_eq S.ρ0 hm h0 b
    unfold pair PreparedData.μ0 at hb0
    rw [this] at hb0
    simpa [mul_comm] using hb0
  refine ⟨fun x => mul_nonneg (hκ x).le (h0 x), by fun_prop, ?_⟩
  have e : (fun x => (1 + κ * b x) * S.ρ0 x) = fun x => S.ρ0 x + κ * (b x * S.ρ0 x) := by
    funext x; ring
  have hbr : Integrable (fun x => b x * S.ρ0 x) := hint _ (hbc.mul hρc)
  rw [e, integral_add (f := fun x => S.ρ0 x) (g := fun x => κ * (b x * S.ρ0 x)) (hint _ hρc)
    (hbr.const_mul κ), integral_const_mul, hbρ, S.hρ0.density.integral_one]
  ring

/-- Example 2.6, first assertion: the mixture is a probability measure with first marginal `μ°`. -/
theorem therm_mixture_marginal (S : PreparedData d) {b : Torus d → ℝ} (hb : Torus.IsSmooth b)
    (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hpos : ∀ x, |a₀ * b x| < Real.sqrt N) :
    IsProbabilityMeasure (mixturePrep S.μ0 b a₀ N) ∧ firstMarginal (mixturePrep S.μ0 b a₀ N) = S.μ0 := by
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hbm : Measurable b := hbc.measurable
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hlt : ∀ x, 0 < 1 + a₀ * b x / Real.sqrt N := fun x => by
    have := (abs_lt.1 (hpos x)).1
    have : -1 < a₀ * b x / Real.sqrt N := by rw [lt_div_iff₀ hN0]; linarith
    linarith
  have hlt' : ∀ x, 0 < 1 - a₀ * b x / Real.sqrt N := fun x => by
    have := (abs_lt.1 (hpos x)).2
    have : a₀ * b x / Real.sqrt N < 1 := by rw [div_lt_iff₀ hN0]; linarith
    linarith
  have hdp : IsProbDensity (fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x) := by
    have := therm_mixDensity_prob S hb hb0 (a₀ / Real.sqrt N) (fun x => by
      have := hlt x; rwa [div_mul_eq_mul_div])
    simpa [div_mul_eq_mul_div] using this
  have hdm : IsProbDensity (fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x) := by
    have := therm_mixDensity_prob S hb hb0 (-(a₀ / Real.sqrt N)) (fun x => by
      have := hlt' x; rw [neg_mul, ← sub_eq_add_neg, div_mul_eq_mul_div]; exact this)
    simpa [div_mul_eq_mul_div, sub_eq_add_neg] using this
  have := HRS.isProb_withDensityReal hdp
  have := HRS.isProb_withDensityReal hdm
  rw [therm_mixturePrep_eq S b hbm a₀ N]
  set Pp := Measure.pi (fun _ : Fin N => withDensityReal fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x)
    with hPp
  set Pm := Measure.pi (fun _ : Fin N => withDensityReal fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x)
    with hPm
  have : IsProbabilityMeasure Pp := by rw [hPp]; infer_instance
  have : IsProbabilityMeasure Pm := by rw [hPm]; infer_instance
  have h2 : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  refine ⟨⟨?_⟩, ?_⟩
  · simp [h2]
  · have hN' : 0 < N := hN
    unfold firstMarginal
    rw [dif_pos hN', Measure.map_add _ _ (measurable_pi_apply _), Measure.map_smul, Measure.map_smul]
    have e1 : Pp.map (fun X : Config d N => X ⟨0, hN'⟩) =
        withDensityReal fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x := by
      have := Measure.pi_map_eval (fun _ : Fin N =>
        withDensityReal fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x) ⟨0, hN'⟩
      simpa using this
    have e2 : Pm.map (fun X : Config d N => X ⟨0, hN'⟩) =
        withDensityReal fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x := by
      have := Measure.pi_map_eval (fun _ : Fin N =>
        withDensityReal fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x) ⟨0, hN'⟩
      simpa using this
    rw [e1, e2]
    have hρ0 := S.hρ0.density.nonneg
    have hρm := S.hρ0.density.measurable
    have hp : withDensityReal (fun x => (1 + a₀ * b x / Real.sqrt N) * S.ρ0 x) =
        S.μ0.withDensity (fun x => ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N)) := by
      unfold PreparedData.μ0; rw [therm_withDensity_eq hρ0 hρm (by fun_prop)]
    have hm' : withDensityReal (fun x => (1 - a₀ * b x / Real.sqrt N) * S.ρ0 x) =
        S.μ0.withDensity (fun x => ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N)) := by
      unfold PreparedData.μ0; rw [therm_withDensity_eq hρ0 hρm (by fun_prop)]
    rw [hp, hm']
    ext s hs
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [withDensity_apply _ hs, withDensity_apply _ hs, ← lintegral_const_mul' _ _ (by simp),
      ← lintegral_const_mul' _ _ (by simp), ← lintegral_add_left' (by
        exact (ENNReal.measurable_ofReal.comp (by fun_prop)).const_mul _ |>.aemeasurable)]
    have : ∀ x, (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N) +
        (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N) = 1 := fun x => by
      rw [← mul_add, ← ENNReal.ofReal_add (hlt x).le (hlt' x).le]
      have : (1 + a₀ * b x / Real.sqrt N + (1 - a₀ * b x / Real.sqrt N)) = 2 := by ring
      rw [this]
      simp [ENNReal.ofReal_ofNat]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    simp_rw [this]
    simp
    all_goals exact (measurable_pi_apply _).aemeasurable

end Main

end HRS
