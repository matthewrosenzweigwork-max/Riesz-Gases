import HRS.MS.Fp81S21TimeRep2
import HRS.MS.Fp81S21WeightedMoments

/-! Product and sample-section bounds for a `MomentRep` on a time slab. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.MS.R26T6

/-- A moment representative has product L² membership and almost every
sample section is time L². Its product second moment is at most `H * M`. -/
theorem fp81s21_MomentRep_time_product
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ) (q : ℝ → Ω → r26t6_Coeff)
    (M a H : ℝ) (hrep : fp81s21_MomentRep E P Q q M)
    (ha : 0 ≤ a) (hH : 0 ≤ H) :
    let dt := volume.restrict (Set.Icc (0 : ℝ) H)
    MemLp (fun p : ℝ × Ω => q (a + p.1) p.2) 2 (dt.prod P) ∧
      (∫ p : ℝ × Ω, ‖q (a + p.1) p.2‖ ^ 2 ∂dt.prod P) ≤ H * M ∧
      ∀ᵐ ω ∂P, MemLp (fun t => q (a + t) ω) 2 dt := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun p => q (a + p.1) p.2
  have hgm : Measurable g := hrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hsec : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 P ∧
      (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨(hrep.2 (a+t) (add_nonneg ha ht.1)).1,
      (hrep.2 (a+t) (add_nonneg ha ht.1)).2.1⟩
  obtain ⟨hg, hb⟩ := fp81s21_memLp_prod_of_section_bound dt P g hgm M hsec
  have hi : Integrable (fun p => ‖g p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  refine ⟨hg, ?_, ?_⟩
  · simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hH] using hb
  · filter_upwards [hi.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_MomentRep_time_product
