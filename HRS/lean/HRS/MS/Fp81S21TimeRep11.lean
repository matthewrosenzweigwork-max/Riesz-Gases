import HRS.MS.Fp81S21TimeRep9

/-! Second moments of projected time-section errors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance fp81s21_timeRep11_lp_measurableSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Integrating fixed-time projection errors gives the corresponding time-L²
error moment bound. -/
theorem fp81s21_time_projection_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hcore : fp81s21_TimeL2Rep P q M a H U)
    (ha : 0 ≤ a) (hH : 0 ≤ H) (m : ℕ) (ε : ℝ)
    (htail : ∀ u, 0 ≤ u →
      Integrable (fun ω => ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2) P ∧
      (∫ ω, ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2 ∂P) ≤ M * ε ^ 2) :
    Integrable (fun ω => ‖U ω - fp81s21_timeProject H m (U ω)‖ ^ 2) P ∧
    (∫ ω, ‖U ω - fp81s21_timeProject H m (U ω)‖ ^ 2 ∂P) ≤ H * M * ε ^ 2 := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z =>
    q (a + z.1) z.2 - fp81s21_projectField m (q (a + z.1) z.2)
  have hq' : Measurable (fun z : ℝ × Ω => q (a + z.1) z.2) :=
    hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgm : Measurable g := hq'.sub ((fp81s21_projectField m).continuous.measurable.comp hq')
  have hsec : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 P ∧
      (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ M * ε ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := htail (a + t) (add_nonneg ha ht.1)
    exact ⟨(memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 hh.1, hh.2⟩
  obtain ⟨hg, hb⟩ := fp81s21_memLp_prod_of_section_bound dt P g hgm (M * ε ^ 2) hsec
  let V : Ω → Lp r26t6_Coeff 2 dt := fun ω => U ω - fp81s21_timeProject H m (U ω)
  have hVL : MemLp V 2 P := hcore.2.1.sub (hcore.2.1.continuousLinearMap_comp (fp81s21_timeProject H m))
  have hVeq : ∀ᵐ ω ∂P, ⇑(V ω) =ᵐ[dt] fun t => g (t, ω) := by
    filter_upwards [hcore.2.2.2] with ω hω
    filter_upwards [hω.2, Lp.coeFn_sub (U ω) (fp81s21_timeProject H m (U ω)),
      fp81s21_timeProject_apply H m (U ω)] with t he hs hp
    change (U ω - fp81s21_timeProject H m (U ω)) t = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hp, he]
  obtain ⟨_, heq⟩ := fp81s21_time_section_moment P H g V hVL.aestronglyMeasurable hg hVeq
  refine ⟨hVL.norm.integrable_sq, ?_⟩
  calc
    _ = ∫ z, ‖g z‖ ^ 2 ∂dt.prod P := heq
    _ ≤ (dt Set.univ).toReal * (M * ε ^ 2) := hb
    _ = H * M * ε ^ 2 := by
      simp [dt, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal hH]
      ring

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_time_projection_second_moment
