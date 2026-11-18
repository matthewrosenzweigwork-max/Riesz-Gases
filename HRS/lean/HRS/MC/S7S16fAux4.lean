import HRS.MC.Sec7Vocab

/-!
# Packet `slow_correction` (S16f), part 4: generic bounded tilts

`s16f_tilt Q g = (int ofReal g dQ)^{-1} . (Q with density ofReal g)` (the shape of `s7_tiltedLaw`) for a probability measure
`Q` and a measurable `g` with `1 <= g <= M`: it is a probability measure, absolutely continuous with density bounded by `M`
(w.r.t. `Q`), and `int F d(tilt) = (int g F dQ)/(int g dQ)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16f

variable {α : Type*} [MeasurableSpace α]

/-- the normalised tilt of `Q` by `g` -/
def s16f_tilt (Q : Measure α) (g : α → ℝ) : Measure α :=
  (∫⁻ x, ENNReal.ofReal (g x) ∂Q)⁻¹ • Q.withDensity fun x => ENNReal.ofReal (g x)

section
variable (Q : Measure α) [IsProbabilityMeasure Q] {g : α → ℝ}

theorem s16f_tilt_Z (hg1 : ∀ x, 1 ≤ g x) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    1 ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂Q ∧ ∫⁻ x, ENNReal.ofReal (g x) ∂Q ≠ ⊤ := by
  constructor
  · calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Q := by simp
      _ ≤ _ := lintegral_mono fun x => by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hg1 x)
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
    calc ∫⁻ x, ENNReal.ofReal (g x) ∂Q ≤ ∫⁻ _, ENNReal.ofReal M ∂Q :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hM x)
      _ = ENNReal.ofReal M := by simp

theorem s16f_tilt_isProb (hg1 : ∀ x, 1 ≤ g x) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    IsProbabilityMeasure (s16f_tilt Q g) := by
  obtain ⟨h1, htop⟩ := s16f_tilt_Z Q hg1 hM
  refine ⟨?_⟩
  unfold s16f_tilt
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (lt_of_lt_of_le one_pos h1).ne' htop

theorem s16f_tilt_rn (hgm : Measurable g) (hg1 : ∀ x, 1 ≤ g x) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    s16f_tilt Q g ≪ Q ∧ ∀ᵐ x ∂Q, (s16f_tilt Q g).rnDeriv Q x ≤ ENNReal.ofReal M := by
  obtain ⟨h1, htop⟩ := s16f_tilt_Z Q hg1 hM
  have hZ0 : (∫⁻ x, ENNReal.ofReal (g x) ∂Q) ≠ 0 := (lt_of_lt_of_le one_pos h1).ne'
  have hwm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgm
  constructor
  · intro A hA
    unfold s16f_tilt
    rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hA, smul_zero]
  · haveI : IsFiniteMeasure (Q.withDensity fun x => ENNReal.ofReal (g x)) :=
      isFiniteMeasure_withDensity htop
    have h2 := Measure.rnDeriv_smul_left_of_ne_top (Q.withDensity fun x => ENNReal.ofReal (g x)) Q
      (r := (∫⁻ x, ENNReal.ofReal (g x) ∂Q)⁻¹) (ENNReal.inv_ne_top.2 hZ0)
    have h3 := Measure.rnDeriv_withDensity Q hwm
    filter_upwards [h2, h3] with x hx2 hx3
    unfold s16f_tilt
    rw [hx2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx3]
    calc (∫⁻ x, ENNReal.ofReal (g x) ∂Q)⁻¹ * ENNReal.ofReal (g x)
        ≤ 1 * ENNReal.ofReal (g x) := by
          gcongr
          exact ENNReal.inv_le_one.2 h1
      _ ≤ ENNReal.ofReal M := by
          rw [one_mul]; exact ENNReal.ofReal_le_ofReal (hM x)

theorem s16f_tilt_integral (hgm : Measurable g) (hg1 : ∀ x, 1 ≤ g x) {M : ℝ} (hM : ∀ x, g x ≤ M)
    {F : α → ℝ} (hF : Integrable F Q) :
    ∫ x, F x ∂(s16f_tilt Q g) = (∫ x, g x * F x ∂Q) / (∫ x, g x ∂Q) := by
  obtain ⟨h1, htop⟩ := s16f_tilt_Z Q hg1 hM
  have hg0 : ∀ x, 0 ≤ g x := fun x => zero_le_one.trans (hg1 x)
  have hmeas : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgm
  have hgi : Integrable g Q :=
    Integrable.of_bound hgm.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hM x)
  have hint0 : 0 ≤ ∫ x, g x ∂Q := integral_nonneg hg0
  have hlin : (∫⁻ a, ENNReal.ofReal (g a) ∂Q).toReal = ∫ x, g x ∂Q := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0),
      ENNReal.toReal_ofReal hint0]
  unfold s16f_tilt
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) F, ENNReal.toReal_inv, hlin]
  have hcongr : (∫ x, (ENNReal.ofReal (g x)).toReal • F x ∂Q) = ∫ x, g x * F x ∂Q := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg0 x)]
  rw [hcongr, smul_eq_mul, div_eq_inv_mul]

end

end HRS.MC.Sec7.S16f

end
