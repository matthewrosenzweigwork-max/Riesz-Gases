import HRS.Commutator.Whole.LocalAuxSAMP2Pot

/-!
# CMX-SAMP (`potentialSobolev`), part 3: smoothness of `σ̂` for admissible `σ`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma contDiff_fm (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun y : Euc d => ‖y‖ ^ n) μ) : ContDiff ℝ ∞ (fm μ) := by
  have h := VectorFourier.contDiff_fourierIntegral (E := ℂ) (μ := μ) (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    (f := fun _ => (1 : ℂ)) (N := (⊤ : ℕ∞)) (fun n _ => by simpa using hmom n)
  convert h using 1
  funext ξ
  simp only [fm, VectorFourier.fourierIntegral]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [Circle.smul_def, smul_eq_mul, mul_one, Real.fourierChar_apply]
  congr 2
  have e : ((ContinuousLinearMap.toLinearMap₁₂ (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) y) ξ =
      inner ℝ y ξ := rfl
  rw [e]
  push_cast
  ring

lemma moments_density {φ : SchwartzMap (Euc d) ℂ} {b : Euc d → ℝ} (hb : Continuous b)
    (hbφ : ∀ x, |b x| ≤ ‖φ x‖) (n : ℕ) :
    Integrable (fun y : Euc d => ‖y‖ ^ n) (volume.withDensity fun x => ENNReal.ofReal (b x)) := by
  rw [integrable_withDensity_iff_integrable_smul' hb.measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine (φ.integrable_pow_mul (volume : Measure (Euc d)) n).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((hb.measurable.ennreal_ofReal.ennreal_toReal).smul
      (measurable_norm.pow_const n)).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ n), mul_comm]
    have h1 : ‖(ENNReal.ofReal (b x)).toReal‖ ≤ ‖φ x‖ := by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_ofReal']
      exact max_le ((le_abs_self _).trans (hbφ x)) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma moments_admissible (σ : SMeas d) (h : IsAdmissible σ) (n : ℕ) :
    Integrable (fun y : Euc d => ‖y‖ ^ n) σ.pos ∧ Integrable (fun y : Euc d => ‖y‖ ^ n) σ.neg := by
  obtain ⟨⟨hp, hn⟩, h2⟩ := h
  rcases h2 with ⟨R, hRp, hRn⟩ | ⟨a, ⟨φ, hφ⟩, rfl⟩
  · have key : ∀ μ : Measure (Euc d), IsFiniteMeasure μ → μ (closedBall (0 : Euc d) R)ᶜ = 0 →
        Integrable (fun y : Euc d => ‖y‖ ^ n) μ := by
      intro μ hμ h0
      refine (integrable_const (R ^ n)).mono' (measurable_norm.pow_const n).aestronglyMeasurable ?_
      have : ∀ᵐ y ∂μ, y ∈ closedBall (0 : Euc d) R := by
        exact ae_iff.2 h0
      filter_upwards [this] with y hy
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hy) n
    exact ⟨key _ hp hRp, key _ hn hRn⟩
  · have hac : Continuous a := by
      have : a = fun x => (φ x).re := by funext x; rw [hφ x]; simp
      rw [this]; exact Complex.continuous_re.comp φ.continuous
    have hφa : ∀ x, |a x| = ‖φ x‖ := by
      intro x; rw [hφ x, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨moments_density hac (fun x => (hφa x).le) n,
      moments_density (φ := φ) hac.neg (fun x => by simp only [Pi.neg_apply, abs_neg]; exact (hφa x).le) n⟩

end HRS.Commutator.Whole.SAMP2
