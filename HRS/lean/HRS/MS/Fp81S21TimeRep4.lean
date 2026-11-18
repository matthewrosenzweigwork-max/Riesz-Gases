import HRS.MS.Fp81S21TimeRep3

/-! The generic part of the time-slab L² construction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A jointly measurable field with a uniform second-moment bound on a
finite interval has product L² membership and almost every sample section
is time L². -/
theorem fp81s21_time_product_of_section_bound
    {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ × Ω → F)
    (hq : Measurable q) (M a H : ℝ) (hH : 0 ≤ H)
    (hsec : ∀ u ∈ Set.Icc a (a + H),
      MemLp (fun ω => q (u, ω)) 2 P ∧
        (∫ ω, ‖q (u, ω)‖ ^ 2 ∂P) ≤ M) :
    let dt := volume.restrict (Set.Icc (0 : ℝ) H)
    MemLp (fun p : ℝ × Ω => q (a + p.1, p.2)) 2 (dt.prod P) ∧
      (∫ p : ℝ × Ω, ‖q (a + p.1, p.2)‖ ^ 2 ∂dt.prod P) ≤ H * M ∧
      ∀ᵐ ω ∂P, MemLp (fun t => q (a + t, ω)) 2 dt := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → F := fun p => q (a + p.1, p.2)
  have hgm : Measurable g := hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hs : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 P ∧
      (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hsec (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hg, hb⟩ := fp81s21_memLp_prod_of_section_bound dt P g hgm M hs
  have hi : Integrable (fun p => ‖g p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  refine ⟨hg, ?_, ?_⟩
  · simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hH] using hb
  · filter_upwards [hi.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_time_product_of_section_bound
