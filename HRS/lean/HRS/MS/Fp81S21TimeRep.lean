import HRS.MS.ProClosureS111FieldL2

/-! Product L² membership from uniform sectional second moments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A measurable field with uniformly bounded sectional second moments belongs
 to product L², with the corresponding integrated bound. -/
theorem fp81s21_memLp_prod_of_section_bound
    {T Ω F : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (dt : Measure T) [IsFiniteMeasure dt]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : T × Ω → F) (hq : Measurable q) (M : ℝ)
    (hsec : ∀ᵐ t ∂dt, MemLp (fun ω => q (t, ω)) 2 P ∧
      (∫ ω, ‖q (t, ω)‖ ^ 2 ∂P) ≤ M) :
    MemLp q 2 (dt.prod P) ∧
      (∫ p, ‖q p‖ ^ 2 ∂dt.prod P) ≤ (dt Set.univ).toReal * M := by
  have hm : AEStronglyMeasurable (fun p => ‖q p‖ ^ 2) (dt.prod P) :=
    (hq.norm.pow_const 2).aestronglyMeasurable
  have hnorm : Integrable (fun t => ∫ ω, ‖‖q (t, ω)‖ ^ 2‖ ∂P) dt := by
    refine (integrable_const M).mono' hm.norm.integral_prod_right' ?_
    filter_upwards [hsec] with t ht
    have he : (∫ ω, ‖‖q (t, ω)‖ ^ 2‖ ∂P) = ∫ ω, ‖q (t, ω)‖ ^ 2 ∂P :=
      integral_congr_ae (ae_of_all P fun ω => Real.norm_of_nonneg (sq_nonneg _))
    have hn : (0 : ℝ) ≤ ∫ ω, ‖q (t, ω)‖ ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    rw [he, Real.norm_of_nonneg hn]
    exact ht.2
  have hi : Integrable (fun p => ‖q p‖ ^ 2) (dt.prod P) :=
    (integrable_prod_iff hm).2 ⟨hsec.mono (fun t ht =>
      (memLp_two_iff_integrable_sq_norm ht.1.aestronglyMeasurable).1 ht.1), hnorm⟩
  refine ⟨(memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).2 hi, ?_⟩
  calc
    _ = ∫ t, ∫ ω, ‖q (t, ω)‖ ^ 2 ∂P ∂dt := integral_prod _ hi
    _ ≤ ∫ t, M ∂dt := integral_mono_ae hi.integral_prod_left
      (integrable_const M) (hsec.mono (fun _ ht => ht.2))
    _ = (dt Set.univ).toReal * M := by rw [integral_const]; simp [Measure.real]

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_memLp_prod_of_section_bound
