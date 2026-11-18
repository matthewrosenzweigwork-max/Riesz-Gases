import HRS.Commutator.Torus.LEIBTAux9

/-!
# LEIB-T helpers, part 10: Fourier transform of a cut-off almost periodic function
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_norm_e (a y : 𝔼) : ‖leibt_e a y‖ = 1 := by
  unfold leibt_e
  exact Complex.norm_exp_ofReal_mul_I _

lemma leibt_continuous_e (a : 𝔼) : Continuous (leibt_e a) := by
  unfold leibt_e
  fun_prop

lemma leibt_e_comm (a y : 𝔼) : leibt_e a y = leibt_e y a := by
  unfold leibt_e
  rw [real_inner_comm]

/-- Fourier transform of the cut-off series. -/
lemma leibt_series_fourier (χ : SchwartzMap 𝔼 ℂ) {N : ℝ} (hN : 0 < N) {ι : Type*} [Countable ι]
    (c : ι → ℂ) (lam : ι → 𝔼) (hc : Summable fun i => ‖c i‖)
    (W : SchwartzMap 𝔼 ℂ) (hW : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (W y))
    (ξ : 𝔼) :
    HasSum (fun i => c i * (((N ^ d : ℝ) : ℂ) * 𝓕 (⇑χ) (N • (ξ - lam i)))) (𝓕 (⇑W) ξ) := by
  set F : ι → 𝔼 → ℂ := fun i y => Complex.exp (((-2 * Real.pi * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I) *
    (c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) with hF
  have hχN : Integrable (fun y : 𝔼 => χ (N⁻¹ • y)) := χ.integrable.comp_smul (inv_ne_zero hN.ne')
  have hnormF : ∀ i y, ‖F i y‖ = ‖c i‖ * ‖χ (N⁻¹ • y)‖ := by
    intro i y
    simp only [hF, norm_mul]
    rw [Complex.norm_exp_ofReal_mul_I, leibt_norm_e]
    ring
  have hcontF : ∀ i, Continuous (F i) := by
    intro i
    have := leibt_continuous_e (lam i)
    simp only [hF]
    fun_prop
  have hFint : ∀ i, Integrable (F i) := by
    intro i
    refine ((hχN.norm.const_mul ‖c i‖)).mono' (hcontF i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (hnormF i y).le)
  have hFnorm : ∀ i, ∫ y, ‖F i y‖ = ‖c i‖ * ((N ^ d : ℝ) * ∫ y : 𝔼, ‖χ y‖) := by
    intro i
    simp_rw [hnormF]
    rw [integral_const_mul]
    congr 1
    have := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure 𝔼) (fun y : 𝔼 => ‖χ y‖) hN.le
    rw [finrank_euclideanSpace_fin] at this
    simpa using this
  have hsum : Summable fun i => ∫ y, ‖F i y‖ := by
    simp_rw [hFnorm]
    exact hc.mul_right _
  have h1 := hasSum_integral_of_summable_integral_norm hFint hsum
  have h2 : ∀ y, ∑' i, F i y = Complex.exp (((-2 * Real.pi * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I) * W y := by
    intro y
    exact ((hW y).mul_left _).tsum_eq
  have h3 : ∀ i, ∫ y, F i y = c i * (((N ^ d : ℝ) : ℂ) * 𝓕 (⇑χ) (N • (ξ - lam i))) := by
    intro i
    have := leibt_fourier_modcut (⇑χ) hN (lam i) ξ
    rw [Real.fourier_eq'] at this
    simp only [hF]
    have e : ∀ y : 𝔼, Complex.exp (((-2 * Real.pi * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I) *
        (c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) =
        c i * (Complex.exp (((-2 * Real.pi * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I) *
          (leibt_e (lam i) y * χ (N⁻¹ • y))) := fun y => by ring
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
  have h4 : ∫ y, ∑' i, F i y = 𝓕 (⇑W) ξ := by
    simp_rw [h2]
    rw [Real.fourier_eq']
    rfl
  rw [h4] at h1
  simpa only [h3] using h1

end HRS.Commutator.TorusNote
