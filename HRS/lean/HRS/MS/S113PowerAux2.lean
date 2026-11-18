import HRS.MS.S113PowerAux1

/-!
# S11.3.E2 (breakdown packet E2): probability normalization and exact entropy of the power tilt
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

section Entropy

variable {α : Type*} [MeasurableSpace α]

theorem s113_power_entropy (Q : Measure α) [IsProbabilityMeasure Q]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (p B : ℝ) (hp : 1 < p) (hB : ∀ x, r x ≤ B)
    (hM : 0 < s113_powerMass Q r p) :
    IsProbabilityMeasure (s113_powerTilt Q r p) ∧
      s113_powerTilt Q r p ≪ Q ∧
      InformationTheory.klDiv (s113_powerTilt Q r p) Q ≠ ⊤ ∧
      Integrable (fun x => Real.log (r x)) (s113_powerTilt Q r p) ∧
      (InformationTheory.klDiv (s113_powerTilt Q r p) Q).toReal =
        p * (∫ x, Real.log (r x) ∂(s113_powerTilt Q r p)) -
          Real.log (s113_powerMass Q r p) := by
  obtain ⟨hi1, hi2, -⟩ := s113_power_integrable Q r hr hr0 p B hp hB
  set M := s113_powerMass Q r p with hMdef
  have hMeq : ∫ x, r x ^ p ∂Q = M := rfl
  have hpow_nn : ∀ x, 0 ≤ r x ^ p / M := fun x => div_nonneg (Real.rpow_nonneg (hr0 x) p) hM.le
  have hdm : Measurable fun x => ENNReal.ofReal (r x ^ p / M) :=
    ENNReal.measurable_ofReal.comp ((hr.pow_const p).div_const M)
  have hint_d : Integrable (fun x => r x ^ p / M) Q := hi1.div_const M
  have hprob : IsProbabilityMeasure (s113_powerTilt Q r p) := by
    refine ⟨?_⟩
    unfold s113_powerTilt
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint_d (Filter.Eventually.of_forall hpow_nn)]
    have : ∫ x, r x ^ p / M ∂Q = 1 := by
      rw [integral_div, hMeq]; exact div_self hM.ne'
    rw [this]; simp
  have hac : s113_powerTilt Q r p ≪ Q := withDensity_absolutelyContinuous Q _
  -- log r is integrable against the tilt
  have hlogint : Integrable (fun x => Real.log (r x)) (s113_powerTilt Q r p) := by
    unfold s113_powerTilt
    rw [integrable_withDensity_iff_integrable_smul' hdm (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine (hi2.div_const M).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hpow_nn x)]
    ring
  -- r > 0 almost everywhere for the tilt
  have hpos : ∀ᵐ x ∂(s113_powerTilt Q r p), r x ≠ 0 := by
    unfold s113_powerTilt
    rw [ae_withDensity_iff hdm]
    refine Filter.Eventually.of_forall fun x hx hx0 => ?_
    apply hx
    rw [hx0, Real.zero_rpow (by linarith : p ≠ 0)]
    simp
  have hrn : (s113_powerTilt Q r p).rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (r x ^ p / M) :=
    Measure.rnDeriv_withDensity Q hdm
  have hllr : llr (s113_powerTilt Q r p) Q =ᵐ[s113_powerTilt Q r p]
      fun x => p * Real.log (r x) - Real.log M := by
    filter_upwards [hac.ae_le hrn, hpos] with x hx hx0
    unfold llr
    rw [hx, ENNReal.toReal_ofReal (hpow_nn x)]
    have hrpos : 0 < r x := lt_of_le_of_ne (hr0 x) (Ne.symm hx0)
    rw [Real.log_div (Real.rpow_pos_of_pos hrpos p).ne' hM.ne', Real.log_rpow hrpos]
  have hint_llr : Integrable (llr (s113_powerTilt Q r p) Q) (s113_powerTilt Q r p) := by
    refine Integrable.congr ?_ hllr.symm
    exact (hlogint.const_mul p).sub (integrable_const _)
  have hkl : InformationTheory.klDiv (s113_powerTilt Q r p) Q ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint_llr
  refine ⟨hprob, hac, hkl, hlogint, ?_⟩
  rw [InformationTheory.toReal_klDiv hac hint_llr, integral_congr_ae hllr,
    integral_sub (hlogint.const_mul p) (integrable_const _), integral_const_mul, integral_const]
  simp

end Entropy

end HRS.MS.S113BD
