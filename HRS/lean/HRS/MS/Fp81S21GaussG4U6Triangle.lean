import HRS.MS.FldRemCen4

/-! A triangular time restriction is controlled by the full energy interval. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21

theorem fp81s21_g4_triangle_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (w q : ℝ) (h : ℝ × X → ℝ≥0∞) :
    (∫⁻ z, (Iic q ×ˢ (univ : Set X)).indicator h z
      ∂((volume.restrict (Icc (0 : ℝ) w)).prod μ)) ≤
    ∫⁻ z, h z ∂((volume.restrict (Icc (0 : ℝ) q)).prod μ) := by
  have hset : (Iic q ×ˢ (univ : Set X)) ∩ (Icc (0 : ℝ) w ×ˢ (univ : Set X)) ⊆
      Icc (0 : ℝ) q ×ˢ (univ : Set X) := by
    intro z hz
    exact ⟨⟨hz.2.1.1, hz.1.1⟩, mem_univ _⟩
  rw [lintegral_indicator (measurableSet_Iic.prod MeasurableSet.univ)]
  apply lintegral_mono' _ le_rfl
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict
    (measurableSet_Iic.prod MeasurableSet.univ), Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono hset le_rfl

#print axioms fp81s21_g4_triangle_lintegral
end HRS.Fp81.S21
end
