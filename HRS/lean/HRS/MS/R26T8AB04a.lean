import HRS.MS.R26T8AV13
import HRS.MS.R26T8AB01

/-!
# S8.2 T8A B04a: supremum measurability from path continuity, and Minkowski for suprema
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

/-- an a.e. continuous, slice-measurable family has an a.e. measurable supremum -/
theorem r26t8a_b04_sup_meas {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) (T : ℝ)
    (Y : ℝ → Omega → ℝ) (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Y t) P)
    (hc : ∀ᵐ w ∂P, ContinuousOn (fun t => Y t w) (Set.Icc 0 T)) :
    AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P := by
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
  have hYsup : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) = ⨆ q ∈ D, ‖Y q w‖ₑ := by
    filter_upwards [hc] with w hw
    rw [← r26t8a_v13a_sup_dense hw hDs hDd]
    exact (iSup_subtype' (p := fun t => t ∈ Set.Icc (0 : ℝ) T) (f := fun t _ => ‖Y t w‖ₑ)).symm
  exact (AEMeasurable.biSup D hDc fun q hq => (hm q (hDs hq)).enorm).congr (hYsup.mono fun w h => h.symm)

/-- Minkowski for the `L²(P)` norm of the supremum of a difference -/
theorem r26t8a_b04_sup_sub {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) (T : ℝ)
    (Y1 Y2 : ℝ → Omega → ℝ)
    (h1 : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y1 t w‖ₑ) P)
    (h2 : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y2 t w‖ₑ) P) :
    (r26t8a_scalarSupSq P T (fun t w => Y2 t w - Y1 t w)) ^ (1 / 2 : ℝ) ≤
      (r26t8a_scalarSupSq P T Y1) ^ (1 / 2 : ℝ) + (r26t8a_scalarSupSq P T Y2) ^ (1 / 2 : ℝ) := by
  have hle : r26t8a_scalarSupSq P T (fun t w => Y2 t w - Y1 t w) ≤
      ∫⁻ w, ((⨆ t : Set.Icc (0 : ℝ) T, ‖Y1 t w‖ₑ) + (⨆ t : Set.Icc (0 : ℝ) T, ‖Y2 t w‖ₑ)) ^ (2 : ℝ) ∂P := by
    unfold r26t8a_scalarSupSq
    refine lintegral_mono fun w => ?_
    rw [ENNReal.rpow_two]
    gcongr
    refine iSup_le fun t => ?_
    calc ‖Y2 t w - Y1 t w‖ₑ ≤ ‖Y2 t w‖ₑ + ‖Y1 t w‖ₑ := enorm_sub_le
      _ ≤ _ := by
        rw [add_comm]
        exact add_le_add (le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖Y1 t w‖ₑ) t)
          (le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖Y2 t w‖ₑ) t)
  have h := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2) h1 h2 (by norm_num)
  refine (ENNReal.rpow_le_rpow hle (by norm_num)).trans (h.trans (le_of_eq ?_))
  unfold r26t8a_scalarSupSq
  simp only [ENNReal.rpow_two]

end HRS.MS.R26T8A

end
