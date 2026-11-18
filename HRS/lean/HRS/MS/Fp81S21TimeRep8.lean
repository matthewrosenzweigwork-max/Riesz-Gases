import HRS.MS.Fp81S21TimeRep7

/-! Time-section construction and its exact second moment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A product L² field has a measurable random section class with the same
second moment. -/
theorem fp81s21_time_section_exists
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ) (g : ℝ × Ω → r26t6_Coeff) (hgm : Measurable g)
    (hg : MemLp g 2 ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P)) :
    ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      Measurable U ∧ MemLp U 2 P ∧
      (∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
        (fun t => g (t, ω))) ∧
      (∫ ω, ‖U ω‖ ^ 2 ∂P) =
        ∫ z, ‖g z‖ ^ 2 ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hi : Integrable (fun p => ‖g p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hs : ∀ᵐ ω ∂P, MemLp (fun t => g (t, ω)) 2 dt := by
    filter_upwards [hi.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
  obtain ⟨U, hUm, hUs, hUeq⟩ := fp81s21_measurable_lp_sections P dt g hgm hs
  obtain ⟨hUL, hUin⟩ := fp81s21_time_section_moment P H g U hUs.aestronglyMeasurable hg hUeq
  exact ⟨U, hUm, hUL, hUeq, hUin⟩

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_time_section_exists
