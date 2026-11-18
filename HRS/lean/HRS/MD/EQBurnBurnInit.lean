import HRS.MD.EQBurnBurnBase
import HRS.MD.EQInitParticle
import HRS.MD.EQInitGauss

/-!
# EQ-BURN P4, part 3: the initial term

`eqb_init_diff`: from second moments of `f` and `g` to the `L¹` and `L²` norms of `f - g`.
`eqb_init_particle`, `eqb_init_gauss`: transfer of the uniform second moments of EQ-INITMOM to a space `Ω₁` carrying `Y` with Gibbs law
(resp. `η'` with the law of `Z 0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

variable {d : ℕ}

theorem eqb_l1_le_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P) :
    ∫⁻ ω, f ω ∂P ≤ (∫⁻ ω, f ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simpa using hH

theorem eqb_l2_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞) {A : ℝ}
    (hA : 0 ≤ A) (h : ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal A) :
    (∫⁻ ω, f ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Real.sqrt A) := by
  have h2 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal A := by
    simpa [ENNReal.rpow_two] using h
  calc (∫⁻ ω, f ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal A) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt A) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← Real.sqrt_eq_rpow]

theorem eqb_init_diff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (f g : Ω → E) (hf : AEMeasurable f P) (hg : AEMeasurable g P) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal A) (hgB : ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ‖f ω - g ω‖ₑ ∂P ≤ ENNReal.ofReal (Real.sqrt A + Real.sqrt B) ∧
      (∫⁻ ω, ‖f ω - g ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Real.sqrt A + Real.sqrt B) := by
  have hfe : AEMeasurable (fun ω => ‖f ω‖ₑ) P := hf.enorm
  have hge : AEMeasurable (fun ω => ‖g ω‖ₑ) P := hg.enorm
  have hA' := eqb_l2_le P (fun ω => ‖f ω‖ₑ) hA hfA
  have hB' := eqb_l2_le P (fun ω => ‖g ω‖ₑ) hB hgB
  constructor
  · calc ∫⁻ ω, ‖f ω - g ω‖ₑ ∂P ≤ ∫⁻ ω, (‖f ω‖ₑ + ‖g ω‖ₑ) ∂P :=
          lintegral_mono fun ω => enorm_sub_le
      _ = ∫⁻ ω, ‖f ω‖ₑ ∂P + ∫⁻ ω, ‖g ω‖ₑ ∂P := lintegral_add_left' hfe _
      _ ≤ _ := by
          rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
          exact add_le_add ((eqb_l1_le_l2 P _ hfe).trans hA') ((eqb_l1_le_l2 P _ hge).trans hB')
  · calc (∫⁻ ω, ‖f ω - g ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ (∫⁻ ω, (‖f ω‖ₑ + ‖g ω‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow (lintegral_mono fun ω =>
            ENNReal.rpow_le_rpow enorm_sub_le (by norm_num)) (by norm_num)
      _ ≤ (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) + (∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
          ENNReal.lintegral_Lp_add_le hfe hge (by norm_num)
      _ ≤ _ := by
          rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
          exact add_le_add hA' hB'

end HRS.MD.EQBurnBurn

end
