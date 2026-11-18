import HRS.MS.Fp81S21TimeRep5

/-! The norm estimate for a measurable family of time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS.MS.R26T6

/-- Once a strongly measurable family represents the product field's sections,
its second moment is exactly the product second moment. -/
theorem fp81s21_time_section_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ) (g : ℝ × Ω → r26t6_Coeff)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hU : AEStronglyMeasurable U P)
    (hg : MemLp g 2 ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P))
    (heq : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) H)),
      U ω t = g (t, ω)) :
    MemLp U 2 P ∧
      (∫ ω, ‖U ω‖ ^ 2 ∂P) =
        ∫ p : ℝ × Ω, ‖g p‖ ^ 2 ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hi : Integrable (fun p : ℝ × Ω => ‖g p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hs : ∀ᵐ ω ∂P, ‖U ω‖ ^ 2 = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
    filter_upwards [heq] with ω hω
    calc
      ‖U ω‖ ^ 2 = inner ℝ (U ω) (U ω) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ t, inner ℝ (U ω t) (U ω t) ∂dt := L2.inner_def _ _
      _ = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
        apply integral_congr_ae
        filter_upwards [hω] with t ht
        rw [real_inner_self_eq_norm_sq, ht]
  have hsq : Integrable (fun ω => ‖U ω‖ ^ 2) P :=
    hi.integral_prod_right.congr (hs.mono (fun _ h => h.symm))
  refine ⟨(memLp_two_iff_integrable_sq_norm hU).2 hsq, ?_⟩
  calc
    _ = ∫ ω, ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt ∂P := integral_congr_ae hs
    _ = _ := (integral_prod_symm _ hi).symm

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_time_section_moment
