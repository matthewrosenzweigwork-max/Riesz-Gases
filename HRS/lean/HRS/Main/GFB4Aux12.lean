import HRS.Main.GFB4Aux11

/-!
# GFB4, part 12: `Lp` helper lemmas for the Wasserstein comparison
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `‖c‖_{L^p} ≤ ‖c‖_{L²}` on a probability space, for `p ∈ {1,2}`. -/
theorem gfb4_lp_le_two (P : Measure Ω) [IsProbabilityMeasure P] {c : Ω → ℝ≥0∞} (hc : AEMeasurable c P)
    {p : ℝ} (hp : p = 1 ∨ p = 2) :
    (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p) ≤ (∫⁻ ω, c ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  rcases hp with rfl | rfl
  · have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hc
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_mul] at h
    simpa using h
  · exact le_rfl

theorem gfb4_lp_const_mul (P : Measure Ω) {p : ℝ} (hp : 0 < p) (C : ℝ≥0∞) (hC : C ≠ ⊤) (u : Ω → ℝ≥0∞) :
    (∫⁻ ω, (C * u ω) ^ p ∂P) ^ (1 / p) = C * (∫⁻ ω, u ω ^ p ∂P) ^ (1 / p) := by
  have h1 : ∀ ω, (C * u ω) ^ p = C ^ p * u ω ^ p := fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp.le
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hC),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  have : p * (1 / p) = 1 := by field_simp
  rw [this, ENNReal.rpow_one]

end HRS.GF
