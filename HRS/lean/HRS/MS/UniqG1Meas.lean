import Mathlib

/-!
# G1 (part 2): measurability of a supremum of continuous functions on `Icc 0 t`

Route.  Compose each `F i` with the clamp `τ ↦ max 0 (min t τ)` (when `0 ≤ t`), which is continuous
on `ℝ` and maps into `Icc 0 t`, so `G i τ := F i (clamp τ)` is continuous on `ℝ` and bounded above
by the common bound `B`.  The pointwise supremum of such a family is lower semicontinuous
(`lowerSemicontinuous_ciSup`), hence measurable (`LowerSemicontinuous.measurable`).  It agrees with
`⨆ i, F i τ` on `Icc 0 t`, where the clamp is the identity.  If `t < 0` the interval is empty.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.UniqG1

theorem g1_iSup_measurable {ι : Type*} (F : ι → ℝ → ℝ) (t : ℝ)
    (hc : ∀ i, ContinuousOn (F i) (Set.Icc 0 t))
    (hb : ∃ B, ∀ i, ∀ τ ∈ Set.Icc 0 t, F i τ ≤ B)
    (hne : Nonempty ι) :
    AEStronglyMeasurable (fun τ => ⨆ i, F i τ) (volume.restrict (Set.Icc 0 t)) := by
  by_cases ht : 0 ≤ t
  · obtain ⟨B, hB⟩ := hb
    have hcont : Continuous (fun τ : ℝ => max 0 (min t τ)) := by fun_prop
    have hmaps : ∀ τ : ℝ, max 0 (min t τ) ∈ Set.Icc 0 t := fun τ =>
      ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
    have hcI : ∀ τ ∈ Set.Icc 0 t, max 0 (min t τ) = τ := by
      intro τ hτ
      rw [min_eq_right hτ.2, max_eq_right hτ.1]
    have hGc : ∀ i, Continuous (fun τ : ℝ => F i (max 0 (min t τ))) :=
      fun i => (hc i).comp_continuous hcont hmaps
    have hbdd : ∀ τ : ℝ, BddAbove (Set.range fun i => F i (max 0 (min t τ))) := fun τ =>
      ⟨B, by rintro _ ⟨i, rfl⟩; exact hB i _ (hmaps τ)⟩
    have hlsc : LowerSemicontinuous (fun τ : ℝ => ⨆ i, F i (max 0 (min t τ))) :=
      lowerSemicontinuous_ciSup hbdd (fun i => (hGc i).lowerSemicontinuous)
    have hmeas : Measurable (fun τ : ℝ => ⨆ i, F i (max 0 (min t τ))) := hlsc.measurable
    refine hmeas.aestronglyMeasurable.congr
      (ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ => ?_)
    simp only [hcI τ hτ]
  · rw [Set.Icc_eq_empty ht, Measure.restrict_empty]
    exact aestronglyMeasurable_zero_measure _

theorem g1_iSup_bdd {ι : Type*} (F : ι → ℝ → ℝ) (t : ℝ)
    (hb : ∃ B, ∀ i, ∀ τ ∈ Set.Icc 0 t, F i τ ≤ B)
    (hne : Nonempty ι) :
    ∃ B', ∀ τ ∈ Set.Icc 0 t, ⨆ i, F i τ ≤ B' := by
  obtain ⟨B, hB⟩ := hb
  have := hne
  exact ⟨B, fun τ hτ => ciSup_le fun i => hB i τ hτ⟩

end HRS.MS.UniqG1
