import HRS.Prob.Metrics
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# S11.1 packet G0: centered Gaussian laws are closed under almost-sure limits
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Complex
open scoped ENNReal NNReal

namespace HRS.MS.S111BD

/-- scalar case, via characteristic functions -/
theorem s111_g0_scalar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (η : Ω → ℝ)
    (hξ : ∀ n, AEMeasurable (ξ n) P) (hη : AEMeasurable η P) (v : ℕ → ℝ≥0)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ξ n ω) atTop (𝓝 (η ω))) :
    ∃ w : ℝ≥0, P.map η = gaussianReal 0 w := by
  have : IsProbabilityMeasure (P.map η) :=
    ⟨by simp [Measure.map_apply_of_aemeasurable hη MeasurableSet.univ]⟩
  -- characteristic function convergence
  have hcf : ∀ t : ℝ, Tendsto (fun n => Complex.exp (-(((v n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)))
      atTop (𝓝 (charFun (P.map η) t)) := by
    intro t
    have e1 : ∀ n, charFun (P.map (ξ n)) t = ∫ ω, Complex.exp (t * ξ n ω * Complex.I) ∂P := by
      intro n
      rw [charFun_apply_real, integral_map (hξ n) (by fun_prop)]
    have e2 : charFun (P.map η) t = ∫ ω, Complex.exp (t * η ω * Complex.I) ∂P := by
      rw [charFun_apply_real, integral_map hη (by fun_prop)]
    have e3 : ∀ n, charFun (P.map (ξ n)) t = Complex.exp (-(((v n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ)) := by
      intro n
      rw [hlaw n, charFun_gaussianReal]
      congr 1
      push_cast
      ring
    have hd := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω => Complex.exp (t * ξ n ω * Complex.I))
      (f := fun ω => Complex.exp (t * η ω * Complex.I)) (fun _ => (1 : ℝ))
      (fun n => by
        have : AEMeasurable (fun ω => Complex.exp (t * ξ n ω * Complex.I)) P :=
          (by fun_prop : Measurable fun x : ℝ => Complex.exp (t * x * Complex.I)).comp_aemeasurable
            (hξ n)
        exact this.aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun ω => by
        simp [Complex.norm_exp])
      (by
        filter_upwards [hlim] with ω hω
        have : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I) := by fun_prop
        exact (this.tendsto _).comp hω)
    rw [e2]
    exact hd.congr fun n => by rw [← e1 n, e3 n]
  -- continuity at zero: pick t₀
  have hc := (continuous_charFun (μ := P.map η)).continuousAt (x := (0 : ℝ))
  have h1 : charFun (P.map η) 0 = 1 := by simp
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  set t₀ : ℝ := δ / 2 with ht₀
  have ht0pos : 0 < t₀ := by positivity
  have hnear : ‖charFun (P.map η) t₀ - 1‖ < 1 / 2 := by
    have := hδ' (x := t₀) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0pos]; linarith)
    simpa [dist_eq_norm, h1] using this
  have hre : (1 / 2 : ℝ) < (charFun (P.map η) t₀).re := by
    have : |(charFun (P.map η) t₀ - 1).re| ≤ ‖charFun (P.map η) t₀ - 1‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_re, Complex.one_re] at this
    have := (abs_lt.1 (lt_of_le_of_lt this hnear)).1
    linarith
  -- real parts
  have hreal : Tendsto (fun n => Real.exp (-((v n : ℝ) * t₀ ^ 2 / 2))) atTop
      (𝓝 (charFun (P.map η) t₀).re) := by
    have := (Complex.continuous_re.tendsto _).comp (hcf t₀)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re]
  set a : ℝ := (charFun (P.map η) t₀).re with ha
  have hapos : 0 < a := by linarith
  have hlog : Tendsto (fun n => Real.log (Real.exp (-((v n : ℝ) * t₀ ^ 2 / 2)))) atTop
      (𝓝 (Real.log a)) := (Real.continuousAt_log hapos.ne').tendsto.comp hreal
  simp only [Real.log_exp] at hlog
  have ht2 : t₀ ^ 2 ≠ 0 := by positivity
  have key : ∀ n, -(2 : ℝ) / t₀ ^ 2 * -((v n : ℝ) * t₀ ^ 2 / 2) = v n := fun n => by
    field_simp
  have hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (-(2 : ℝ) / t₀ ^ 2 * Real.log a)) :=
    (hlog.const_mul (-(2 : ℝ) / t₀ ^ 2)).congr key
  set vv : ℝ := -(2 : ℝ) / t₀ ^ 2 * Real.log a with hvv
  have hvv0 : 0 ≤ vv := ge_of_tendsto' hvlim fun n => (v n).2
  refine ⟨vv.toNNReal, ?_⟩
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_gaussianReal, Real.coe_toNNReal _ hvv0]
  have h3 : Tendsto (fun n => Complex.exp (-(((v n : ℝ) * t ^ 2 / 2 : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp (-((vv * t ^ 2 / 2 : ℝ) : ℂ)))) := by
    have : Continuous fun x : ℝ => Complex.exp (-((x * t ^ 2 / 2 : ℝ) : ℂ)) := by fun_prop
    exact (this.tendsto _).comp hvlim
  have := tendsto_nhds_unique (hcf t) h3
  rw [this]
  congr 1
  push_cast
  ring

theorem s111_centered_gaussian_ae_limit
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → B) (Y : Ω → B)
    (hXm : ∀ n, AEMeasurable (X n) P) (hYm : AEMeasurable Y P)
    (hX : ∀ n, HRS.IsCenteredGaussian (P.map (X n)))
    (hlim : ∀ᵐ ζ ∂P, Tendsto (fun n => X n ζ) atTop (𝓝 (Y ζ))) :
    HRS.IsCenteredGaussian (P.map Y) := by
  have hmap : ∀ (L : StrongDual ℝ B) {f : Ω → B}, AEMeasurable f P →
      (P.map f).map L = P.map (fun ω => L (f ω)) := fun L f hf =>
    AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hf
  have hsc : ∀ L : StrongDual ℝ B, ∃ w : ℝ≥0, (P.map Y).map L = gaussianReal 0 w := by
    intro L
    have hLX : ∀ n, ∃ w : ℝ≥0, P.map (fun ω => L (X n ω)) = gaussianReal 0 w := by
      intro n
      refine ⟨(Var[L; P.map (X n)]).toNNReal, ?_⟩
      have h1 := (hX n).1.map_eq_gaussianReal L
      have h2 : (P.map (X n))[L] = 0 := (hX n).2 L
      rw [h2, hmap L (hXm n)] at h1
      exact h1
    choose v hv using hLX
    obtain ⟨w, hw⟩ := s111_g0_scalar P (fun n ω => L (X n ω)) (fun ω => L (Y ω))
      (fun n => L.continuous.measurable.comp_aemeasurable (hXm n))
      (L.continuous.measurable.comp_aemeasurable hYm) v hv
      (by
        filter_upwards [hlim] with ω hω
        exact (L.continuous.tendsto _).comp hω)
    exact ⟨w, by rw [hmap L hYm]; exact hw⟩
  have : IsProbabilityMeasure (P.map Y) :=
    ⟨by simp [Measure.map_apply_of_aemeasurable hYm MeasurableSet.univ]⟩
  refine ⟨?_, fun L => ?_⟩
  · refine isGaussian_of_isGaussian_map fun L => ?_
    obtain ⟨w, hw⟩ := hsc L
    rw [hw]
    infer_instance
  · obtain ⟨w, hw⟩ := hsc L
    have := integral_map (μ := P.map Y) L.continuous.measurable.aemeasurable
      (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [hw, integral_id_gaussianReal] at this
    simpa using this.symm

end HRS.MS.S111BD
