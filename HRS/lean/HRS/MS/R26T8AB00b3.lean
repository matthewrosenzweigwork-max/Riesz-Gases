import HRS.MS.R26T8AB00b2

/-!
# S8.2 observed-time layer, packet T8A.B00b (helper 3): the area of the triangle

`(vol|[0,T] × vol|[0,T]) {(v, r) | r ≤ v} = ofReal (T²/2)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00b3_tri_mass (T : ℝ) (hT : 0 ≤ T) :
    ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T)))
      {q : ℝ × ℝ | q.2 ≤ q.1} = ENNReal.ofReal (T ^ 2 / 2) := by
  rw [Measure.prod_apply (measurableSet_le measurable_snd measurable_fst)]
  have h1 : ∀ v ∈ Set.Icc (0 : ℝ) T,
      (volume.restrict (Set.Icc (0 : ℝ) T)) (Prod.mk v ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1}) =
        ENNReal.ofReal v := by
    intro v hv
    have : Prod.mk v ⁻¹' {q : ℝ × ℝ | q.2 ≤ q.1} = Set.Iic v := by ext r; simp
    rw [this, Measure.restrict_apply measurableSet_Iic]
    have h2 : Set.Iic v ∩ Set.Icc 0 T = Set.Icc 0 v := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hv.2⟩
    rw [h2, Real.volume_Icc, sub_zero]
  rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall h1))]
  have hint : IntegrableOn (fun v : ℝ => v) (Set.Icc 0 T) :=
    continuous_id.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => hv.1))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT, integral_id]
  ring

end HRS.MS.R26T8A

end
