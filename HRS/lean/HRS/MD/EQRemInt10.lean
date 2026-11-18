import HRS.MD.EQRemInt9

/-!
# EQ-REM (b), part 10: the weighted second moment bound (Tonelli and Cauchy-Schwarz)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d N : ℕ}

theorem eqrem_second_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ × Ω → Config d N) (hY : Measurable Y) (E : Config d N → ℝ≥0∞) (hE : Measurable E)
    (S : Set ℝ) (hS : MeasurableSet S) (w : ℝ → ℝ≥0∞) (hw : Measurable w) (B0 : ℝ≥0∞)
    (hB : ∀ r ∈ S, ∫⁻ ω, E (Y (r, ω)) ∂P ≤ B0) :
    ∫⁻ ω, (∫⁻ r in S, w r * (E (Y (r, ω))) ^ (1 / 2 : ℝ)) ^ 2 ∂P ≤ (∫⁻ r in S, w r) ^ 2 * B0 := by
  have hjE : Measurable fun p : ℝ × Ω => E (Y p) := hE.comp hY
  have hF : Measurable fun p : ℝ × Ω => w p.1 * E (Y p) := (hw.comp measurable_fst).mul hjE
  have hpt : ∀ ω, (∫⁻ r in S, w r * (E (Y (r, ω))) ^ (1 / 2 : ℝ)) ^ 2 ≤
      (∫⁻ r in S, w r) * (∫⁻ r in S, w r * E (Y (r, ω))) := by
    intro ω
    have hh : Measurable fun r : ℝ => (E (Y (r, ω))) ^ (1 / 2 : ℝ) :=
      (hjE.comp (measurable_id.prodMk measurable_const)).pow_const _
    have := eqrem_cs_w (volume.restrict S) w _ hw hh
    simp only [eqrem_sq_rpow_half] at this
    exact this
  calc ∫⁻ ω, (∫⁻ r in S, w r * (E (Y (r, ω))) ^ (1 / 2 : ℝ)) ^ 2 ∂P
      ≤ ∫⁻ ω, (∫⁻ r in S, w r) * (∫⁻ r in S, w r * E (Y (r, ω))) ∂P := lintegral_mono hpt
    _ = (∫⁻ r in S, w r) * ∫⁻ ω, (∫⁻ r in S, w r * E (Y (r, ω))) ∂P := by
        rw [lintegral_const_mul]
        exact hF.lintegral_prod_left'
    _ = (∫⁻ r in S, w r) * ∫⁻ r in S, (∫⁻ ω, w r * E (Y (r, ω)) ∂P) := by
        rw [lintegral_lintegral_swap]
        exact (hF.comp measurable_swap).aemeasurable
    _ ≤ (∫⁻ r in S, w r) * ∫⁻ r in S, w r * B0 := by
        refine mul_le_mul' le_rfl ?_
        refine setLIntegral_mono' hS fun r hr => ?_
        have hm : Measurable fun ω => E (Y (r, ω)) := hjE.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ hm]
        exact mul_le_mul' le_rfl (hB r hr)
    _ = (∫⁻ r in S, w r) ^ 2 * B0 := by
        rw [lintegral_mul_const _ hw, sq, mul_assoc]

end HRS.MD.EQRem

end
