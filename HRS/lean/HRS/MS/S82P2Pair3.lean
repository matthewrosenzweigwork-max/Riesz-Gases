import HRS.MS.S82P2Pair2

/-!
# S8.2 (S82P2): per-site resampling bound for the pair statistic (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_double_integral {E : Type*} [MeasurableSpace E] {mu : Measure E}
    [IsProbabilityMeasure mu] {u : E → ℝ} (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z)
    {Mom κ : ℝ} (hκ : 0 ≤ κ) (hMom : 0 ≤ Mom) (hJ : ∫⁻ z, ENNReal.ofReal (u z) ∂mu ≤ ENNReal.ofReal Mom) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (κ * (u x + u y)) ∂mu ∂mu ≤ ENNReal.ofReal (2 * κ * Mom) := by
  have hum : Measurable (fun z => ENNReal.ofReal (u z)) := ENNReal.measurable_ofReal.comp hu
  have e : ∀ x, ∫⁻ y, ENNReal.ofReal (κ * (u x + u y)) ∂mu =
      ENNReal.ofReal κ * ENNReal.ofReal (u x) +
        ENNReal.ofReal κ * ∫⁻ y, ENNReal.ofReal (u y) ∂mu := by
    intro x
    have h1 : ∀ y, ENNReal.ofReal (κ * (u x + u y)) =
        ENNReal.ofReal κ * ENNReal.ofReal (u x) + ENNReal.ofReal κ * ENNReal.ofReal (u y) := by
      intro y
      rw [mul_add, ENNReal.ofReal_add (mul_nonneg hκ (hu0 x)) (mul_nonneg hκ (hu0 y)),
        ENNReal.ofReal_mul hκ, ENNReal.ofReal_mul hκ]
    simp_rw [h1]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [e]
  have hm1 : Measurable (fun x => ENNReal.ofReal κ * ENNReal.ofReal (u x)) :=
    measurable_const.mul hum
  rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, measure_univ, mul_one]
  calc ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (u x) ∂mu +
        ENNReal.ofReal κ * ∫⁻ y, ENNReal.ofReal (u y) ∂mu
      ≤ ENNReal.ofReal κ * ENNReal.ofReal Mom + ENNReal.ofReal κ * ENNReal.ofReal Mom := by
        gcongr
    _ = ENNReal.ofReal (2 * κ * Mom) := by
        rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add (mul_nonneg hκ hMom) (mul_nonneg hκ hMom)]
        congr 1
        ring

end HRS.MS.S82P2
