import HRS.MS.R26T8AB00n2
import HRS.MS.CritForceObs1

/-!
# S8.2 observed-time layer, packet T8A.B00 (helper n3): measurability of the anchored supremum

If `Y t w = Y 0 w + ∫_0^t G r w dr` for a.e. `w`, `G` is a.e. strongly measurable on the product and `Y 0` is a.e. measurable,
then `w ↦ sup_{t ∈ [0,T]} ‖Y t w‖ₑ` is a.e. measurable (the extracted measurability half of `s82n_anchored_observed_sup`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00n3_sup_meas {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [SFinite P]
    (T : ℝ) (Y G : ℝ → Omega → ℝ) (hY0m : AEMeasurable (Y 0) P)
    (hGm : AEStronglyMeasurable (fun p : ℝ × Omega => G p.1 p.2)
      ((volume.restrict (Set.Icc 0 T)).prod P))
    (hFTC : ∀ᵐ w ∂P, IntegrableOn (fun t => G t w) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Y t w = Y 0 w + ∫ r in Set.Icc 0 t, G r w) :
    AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  -- each fixed time slice is a.e. measurable
  have hslice : ∀ t : Set.Icc (0 : ℝ) T, AEMeasurable (fun w => Y t w) P := by
    intro t
    have hGt : AEStronglyMeasurable
        (fun p : ℝ × Omega => ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
          (fun p => G p.1 p.2) p) (ν.prod P) :=
      hGm.indicator (measurableSet_Icc.preimage measurable_fst)
    have hint : AEStronglyMeasurable
        (fun w => ∫ r, ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
          (fun p => G p.1 p.2) (r, w) ∂ν) P :=
      hGt.prod_swap.integral_prod_right'
    have heq : ∀ w, (∫ r, ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
          (fun p => G p.1 p.2) (r, w) ∂ν) = ∫ r in Set.Icc 0 (t : ℝ), G r w := by
      intro w
      have : (fun r => ({p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)}).indicator
          (fun p => G p.1 p.2) (r, w)) =
          (Set.Icc (0 : ℝ) t).indicator (fun r => G r w) := by
        funext r
        by_cases hr : r ∈ Set.Icc (0 : ℝ) t
        · rw [Set.indicator_of_mem (show ((r, w) : ℝ × Omega) ∈
            {p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)} from hr), Set.indicator_of_mem hr]
        · rw [Set.indicator_of_notMem (show ((r, w) : ℝ × Omega) ∉
            {p : ℝ × Omega | p.1 ∈ Set.Icc 0 (t : ℝ)} from hr), Set.indicator_of_notMem hr]
      rw [this, integral_indicator measurableSet_Icc, hν, Measure.restrict_restrict measurableSet_Icc,
        Set.inter_eq_left.mpr (Set.Icc_subset_Icc_right t.2.2)]
    have hmeasZ : AEMeasurable (fun w => Y 0 w + ∫ r in Set.Icc 0 (t : ℝ), G r w) P := by
      refine hY0m.add ?_
      have := hint.aemeasurable
      simpa only [heq] using this
    refine hmeasZ.congr ?_
    filter_upwards [hFTC] with w hw
    exact (hw.2 t t.2).symm
  have : Countable D := hDc.to_subtype
  have hsupD : AEMeasurable (fun w => ⨆ t : D, ‖Y (t : Set.Icc (0 : ℝ) T) w‖ₑ) P :=
    AEMeasurable.iSup fun t => (hslice t).enorm
  refine hsupD.congr ?_
  filter_upwards [hFTC] with w hw
  have hcont := HRS.MS.S82N.s82n_primitive_continuous T (fun r => G r w) hw.1 (Y 0 w)
  have hZ := hDd.ciSup' hcont
  calc (⨆ t : D, ‖Y (t : Set.Icc (0 : ℝ) T) w‖ₑ)
      = ⨆ t : D, ‖Y 0 w + ∫ u in Set.Icc 0 ((t : Set.Icc (0 : ℝ) T) : ℝ), G u w‖ₑ :=
        iSup_congr fun t => by rw [hw.2 _ t.1.2]
    _ = ⨆ t : Set.Icc (0 : ℝ) T, ‖Y 0 w + ∫ u in Set.Icc 0 (t : ℝ), G u w‖ₑ := hZ
    _ = ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ :=
        iSup_congr fun t => by rw [hw.2 _ t.2]

end HRS.MS.R26T8A

end
