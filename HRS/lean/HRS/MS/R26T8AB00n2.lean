import HRS.MS.R26T8AB00n1

/-!
# S8.2 observed-time layer, packet T8A.B00 (helper n2): rearranging triple products

For `f t r w` jointly a.e. strongly measurable on `((μ₁ × μ₂) × P)`, the associated function is jointly a.e. strongly measurable on
`μ₁ × (μ₂ × P)`, and the integral over the middle variable is a.e. strongly measurable on `μ₁ × P`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00n2_assoc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ1 μ2 : Measure ℝ) [SFinite μ1] [SFinite μ2] (f : ℝ → ℝ → Ω → ℝ)
    (hf : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => f p.1.1 p.1.2 p.2) ((μ1.prod μ2).prod P)) :
    AEStronglyMeasurable (fun q : ℝ × (ℝ × Ω) => f q.1 q.2.1 q.2.2) (μ1.prod (μ2.prod P)) := by
  have h := (measurePreserving_prodAssoc μ1 μ2 P).symm
  exact hf.comp_quasiMeasurePreserving h.quasiMeasurePreserving

theorem r26t8a_b00n2_mid_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ1 μ2 : Measure ℝ) [SFinite μ1] [SFinite μ2] (f : ℝ → ℝ → Ω → ℝ)
    (hf : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => f p.1.1 p.1.2 p.2) ((μ1.prod μ2).prod P)) :
    AEStronglyMeasurable (fun p : ℝ × Ω => ∫ r, f p.1 r p.2 ∂μ2) (μ1.prod P) := by
  have h1 := r26t8a_b00n2_assoc P μ1 μ2 f hf
  have hsw : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.swap : Ω × ℝ → ℝ × Ω))
      (μ1.prod (P.prod μ2)) (μ1.prod (μ2.prod P)) :=
    MeasurePreserving.prod (MeasurePreserving.id μ1) (Measure.measurePreserving_swap)
  have h2 : AEStronglyMeasurable (fun q : ℝ × (Ω × ℝ) => f q.1 q.2.2 q.2.1) (μ1.prod (P.prod μ2)) :=
    h1.comp_quasiMeasurePreserving hsw.quasiMeasurePreserving
  have h3 : AEStronglyMeasurable (fun q : (ℝ × Ω) × ℝ => f q.1.1 q.2 q.1.2) ((μ1.prod P).prod μ2) :=
    h2.comp_quasiMeasurePreserving (measurePreserving_prodAssoc μ1 P μ2).quasiMeasurePreserving
  exact h3.integral_prod_right'

end HRS.MS.R26T8A

end
