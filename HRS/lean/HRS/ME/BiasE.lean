import HRS.ME.BiasA
import HRS.ME.BiasB
import HRS.ME.BiasC

/-!
# Chunk E, row 2.10 (fixed-`β` closure), packet E: the abstract core of `critical_bias_constants`

For `η = ζ + a` almost surely (`a` deterministic), `‖a - r b‖ ≤ B_c r_N'` and `W_p(Law ζ, Law G) ≤ A N^{-1/2}`
(respectively `d_k(Law ζ, Law G) ≤ A N^{-1/2}`), `r = log N/√N`:
* `core_wasserstein`: `|W_p(Law η, Law G)/r - ‖b‖| ≤ (A N^{-1/2} + B_c √(log N)/√N)/r` and finiteness;
* `core_smooth`: the two displays of clause 2 with error `(A N^{-1/2} + B_c √(log N)/√N + ½ r² ‖b‖²)/r`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

theorem rate_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Real.log N / Real.sqrt N := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  positivity

section Core

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']

/-- Clause 1, abstract. -/
theorem core_wasserstein (ζ η : Ω → B) (G : Ω' → B) (hζ : AEMeasurable ζ P)
    (hG : AEMeasurable G P') (hint : Integrable (fun ω => ‖ζ ω‖) P) (a b : B)
    (hη : η =ᵐ[P] fun ω => ζ ω + a) {N : ℕ} (hN : 2 ≤ N) {A Bc : ℝ} (hA : 0 ≤ A)
    (hshift : ‖a - (Real.log N / Real.sqrt N) • b‖ ≤
      Bc * (Real.sqrt (Real.log N) / Real.sqrt N)) (p : ℝ) (hp : 1 ≤ p)
    (hW : wassersteinE p (law P ζ) (law P' G) ≤ ENNReal.ofReal (A * (N : ℝ) ^ (-(1 : ℝ) / 2))) :
    wassersteinE p (law P η) (law P' G) ≠ ⊤ ∧
      |(wassersteinE p (law P η) (law P' G)).toReal / (Real.log N / Real.sqrt N) - ‖b‖| ≤
        (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N)) /
          (Real.log N / Real.sqrt N) := by
  set r := Real.log N / Real.sqrt N with hr
  have hr0 : 0 < r := rate_pos hN
  haveI : IsProbabilityMeasure (law P' G) := (Measure.isProbabilityMeasure_map_iff hG).2 inferInstance
  have hlaw : law P η = law P (fun ω => ζ ω + a) := Measure.map_congr hη
  have hfin : wassersteinE p (law P ζ) (law P' G) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  obtain ⟨hne, hineq⟩ := wassersteinE_translate_sandwich P ζ hζ hint a (law P' G) p hp hfin
  rw [hlaw]
  refine ⟨hne, ?_⟩
  have hWz : (wassersteinE p (law P ζ) (law P' G)).toReal ≤ A * (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hW
  set W := (wassersteinE p (law P (fun ω => ζ ω + a)) (law P' G)).toReal with hWdef
  have h1 : |W - ‖a‖| ≤ A * (N : ℝ) ^ (-(1 : ℝ) / 2) := hineq.trans hWz
  have h2 : |‖a‖ - r * ‖b‖| ≤ Bc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
    have : ‖r • b‖ = r * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    rw [← this]
    exact (abs_norm_sub_norm_le a (r • b)).trans hshift
  have h3 : |W - r * ‖b‖| ≤ A * (N : ℝ) ^ (-(1 : ℝ) / 2) +
      Bc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
    calc |W - r * ‖b‖| = |(W - ‖a‖) + (‖a‖ - r * ‖b‖)| := by ring_nf
      _ ≤ |W - ‖a‖| + |‖a‖ - r * ‖b‖| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  have e : W / r - ‖b‖ = (W - r * ‖b‖) / r := by field_simp
  rw [e, abs_div, abs_of_pos hr0]
  exact div_le_div_of_nonneg_right h3 hr0.le

/-- Clause 2, abstract. -/
theorem core_smooth (ζ η : Ω → B) (G : Ω' → B) (hζ : AEMeasurable ζ P)
    (hG : AEMeasurable G P') (a b : B) (hη : η =ᵐ[P] fun ω => ζ ω + a) {N : ℕ} (hN : 2 ≤ N)
    {A Bc : ℝ} (k : ℕ) (hk : 2 ≤ k)
    (hshift : ‖a - (Real.log N / Real.sqrt N) • b‖ ≤
      Bc * (Real.sqrt (Real.log N) / Real.sqrt N))
    (hd : smoothDist k (law P ζ) (law P' G) ≤ A * (N : ℝ) ^ (-(1 : ℝ) / 2)) :
    (∀ Φ : B → ℝ, Φ ∈ CbUnitBall B k →
      |(∫ z, Φ z ∂(law P η) - ∫ z, Φ z ∂(law P' G)) / (Real.log N / Real.sqrt N) -
          ∫ ω, fderiv ℝ Φ (G ω) b ∂P'| ≤
        (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N) +
          (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * ‖b‖ ^ 2) / (Real.log N / Real.sqrt N)) ∧
    |smoothDist k (law P η) (law P' G) / (Real.log N / Real.sqrt N) - smoothConstant P' k G b| ≤
      (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N) +
        (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * ‖b‖ ^ 2) / (Real.log N / Real.sqrt N) := by
  set r := Real.log N / Real.sqrt N with hr
  have hr0 : 0 < r := rate_pos hN
  have hlaw : law P η = law P (fun ω => ζ ω + a) := Measure.map_congr hη
  set E := A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N) +
    (1 / 2) * r ^ 2 * ‖b‖ ^ 2 with hE
  have hbd : smoothDist k (law P ζ) (law P' G) + ‖a - r • b‖ + (1 / 2) * r ^ 2 * ‖b‖ ^ 2 ≤ E := by
    rw [hE]; linarith
  refine ⟨fun Φ hΦ => ?_, ?_⟩
  · have hexp := smooth_translation_expansion_sep P P' ζ G hζ hG a b r hr0 k hk Φ hΦ
    have hI : ∫ z, Φ z ∂(law P η) = ∫ ω, Φ (ζ ω + a) ∂P := by
      rw [hlaw]
      exact integral_map (hζ.add_const a) hΦ.1.continuous.aestronglyMeasurable
    rw [hI]
    have e : (∫ ω, Φ (ζ ω + a) ∂P - ∫ z, Φ z ∂(law P' G)) / r - ∫ ω, fderiv ℝ Φ (G ω) b ∂P' =
        (∫ ω, Φ (ζ ω + a) ∂P - ∫ z, Φ z ∂(law P' G) - r * ∫ ω, fderiv ℝ Φ (G ω) b ∂P') / r := by
      field_simp
    have hG' : ∫ z, Φ z ∂(law P' G) = ∫ ω, Φ (G ω) ∂P' :=
      integral_map hG hΦ.1.continuous.aestronglyMeasurable
    rw [e, hG', abs_div, abs_of_pos hr0]
    exact div_le_div_of_nonneg_right (hexp.trans hbd) hr0.le
  · have hdist := smooth_translation_distance_sep P P' ζ G hζ hG a b r hr0 k hk
    rw [← hlaw] at hdist
    have e : smoothDist k (law P η) (law P' G) / r - smoothConstant P' k G b =
        (smoothDist k (law P η) (law P' G) - r * smoothConstant P' k G b) / r := by
      field_simp
    rw [e, abs_div, abs_of_pos hr0]
    exact div_le_div_of_nonneg_right (hdist.trans hbd) hr0.le

end Core

end HRS.ME.Bias
