import HRS.MS.Fp81S21CovSum2

/-!
# S2.1(iii), packet 16b: cumulative continuity from interval domination

This generic continuity principle joins the summed interval estimate to the
DCT-continuous source primitive. A physical block-value cumulative can use it
once its additive interval bound is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter
open scoped ENNReal NNReal BigOperators Topology

namespace HRS.Fp81.S21

/-- A cumulative path controlled by the increments of a finite source
integral is continuous. The scalar control is continuous by dominated
convergence (`fp81s21_continuousOn_lintegral_Ioc`). -/
theorem fp81s21_continuousOn_of_lintegral_modulus
    {E : Type*} [PseudoMetricSpace E]
    {q T : ℝ} (J : ℝ → E) (f : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f volume)
    (hfinite : ∫⁻ t in Icc q T, f t < ∞)
    (hmodulus : ∀ x ∈ Icc q T, ∀ y ∈ Icc q T,
      dist (J y) (J x) ≤
        dist ((∫⁻ t in Ioc q y, f t).toReal)
          ((∫⁻ t in Ioc q x, f t).toReal)) :
    ContinuousOn J (Icc q T) := by
  have hsource : ContinuousOn
      (fun u => (∫⁻ t in Ioc q u, f t).toReal) (Icc q T) := by
    intro x hx
    have hprimitive := fp81s21_continuousOn_lintegral_Ioc f hf hfinite
    have hfiniteX : (∫⁻ t in Ioc q x, f t) < ∞ := by
      have hsub : Ioc q x ⊆ Icc q T := by
        intro t ht
        exact ⟨le_of_lt ht.1, ht.2.trans hx.2⟩
      have hle : (∫⁻ t in Ioc q x, f t) ≤ ∫⁻ t in Icc q T, f t := by
        calc
          (∫⁻ t in Ioc q x, f t) =
              ∫⁻ t, (Ioc q x).indicator f t ∂volume :=
                (lintegral_indicator measurableSet_Ioc f).symm
          _ ≤ ∫⁻ t, (Icc q T).indicator f t ∂volume := by
                apply lintegral_mono
                intro t
                by_cases ht : t ∈ Ioc q x
                · have ht' := hsub ht
                  simp [ht, ht']
                · simp [ht]
          _ = ∫⁻ t in Icc q T, f t :=
                lintegral_indicator measurableSet_Icc f
      exact lt_of_le_of_lt hle hfinite
    have htoReal : ContinuousAt ENNReal.toReal
        (∫⁻ t in Ioc q x, f t) :=
      ENNReal.continuousAt_toReal (x := ∫⁻ t in Ioc q x, f t) (ne_of_lt hfiniteX)
    convert htoReal.comp_continuousWithinAt
      (f := fun u : ℝ => ∫⁻ t in Ioc q u, f t) (hprimitive x hx) using 1 <;> rfl
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hsource x hx) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy hxy
  exact lt_of_le_of_lt (hmodulus x hx y hy) (hδ' hy hxy)

#print axioms fp81s21_continuousOn_of_lintegral_modulus

end HRS.Fp81.S21

end
