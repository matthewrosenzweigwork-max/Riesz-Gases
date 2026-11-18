import HRS.MS.R26T8AB00a1

/-!
# S8.2 observed-time layer, packet T8A.B00a (helper 2): sample-wise bound and Fubini transfer

For a fixed sample, the integral over the parameter of the FTC identity is bounded by `∫⁻ ‖V 0‖ₑ + ∫⁻∫⁻ ‖Vd‖ₑ`
(`r26t8a_b00a2_pt`), and, if `Vd` is jointly integrable, it is the anchored primitive of the parameter integral of `Vd`
(`r26t8a_b00a2_fubini`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00a2_pt (l h T : ℝ) (V0 : ℝ → ℝ) (Vt Vd : ℝ → ℝ → ℝ)
    (hV0 : AEMeasurable (fun r => ‖V0 r‖ₑ) (volume.restrict (Set.Icc l h)))
    (hFTC : ∀ᵐ r ∂(volume.restrict (Set.Icc l h)),
      ∀ t ∈ Set.Icc 0 T, Vt t r = V0 r + ∫ v in Set.Icc 0 t, Vd v r)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖∫ r in Set.Icc l h, Vt t r‖ₑ ≤ (∫⁻ r in Set.Icc l h, ‖V0 r‖ₑ) +
      ∫⁻ r in Set.Icc l h, ∫⁻ v in Set.Icc 0 T, ‖Vd v r‖ₑ := by
  calc ‖∫ r in Set.Icc l h, Vt t r‖ₑ ≤ ∫⁻ r in Set.Icc l h, ‖Vt t r‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Set.Icc l h, (‖V0 r‖ₑ + ∫⁻ v in Set.Icc 0 T, ‖Vd v r‖ₑ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hFTC] with r hr
        rw [hr t ht]
        refine (enorm_add_le _ _).trans (add_le_add_right ?_ _)
        exact (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono_set (Set.Icc_subset_Icc_right ht.2))
    _ = _ := lintegral_add_left' hV0 _

theorem r26t8a_b00a2_fubini (l h T : ℝ) (V0 : ℝ → ℝ) (Vt Vd : ℝ → ℝ → ℝ)
    (hV0 : Integrable V0 (volume.restrict (Set.Icc l h)))
    (hI : Integrable (fun q : ℝ × ℝ => Vd q.1 q.2)
      ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))))
    (hFTC : ∀ᵐ r ∂(volume.restrict (Set.Icc l h)),
      ∀ t ∈ Set.Icc 0 T, Vt t r = V0 r + ∫ v in Set.Icc 0 t, Vd v r) :
    IntegrableOn (fun v => ∫ r in Set.Icc l h, Vd v r) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ∫ r in Set.Icc l h, Vt t r =
        (∫ r in Set.Icc l h, V0 r) + ∫ v in Set.Icc 0 t, ∫ r in Set.Icc l h, Vd v r := by
  refine ⟨hI.integral_prod_left, fun t ht => ?_⟩
  set Ft : ℝ × ℝ → ℝ := fun q => ({q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t}).indicator
    (fun q => Vd q.1 q.2) q with hFt
  have hFtI : Integrable Ft
      ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))) :=
    hI.indicator (measurableSet_Icc.preimage measurable_fst)
  have e1 : ∀ r, ∫ v, Ft (v, r) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) =
      ∫ v in Set.Icc 0 t, Vd v r := by
    intro r
    have : (fun v => Ft (v, r)) = (Set.Icc (0 : ℝ) t).indicator (fun v => Vd v r) := by
      funext v
      by_cases hv : v ∈ Set.Icc (0 : ℝ) t
      · rw [hFt]; simp only [Set.indicator_of_mem (show ((v, r) : ℝ × ℝ) ∈
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv), Set.indicator_of_mem hv]
      · rw [hFt]; simp only [Set.indicator_of_notMem (show ((v, r) : ℝ × ℝ) ∉
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv), Set.indicator_of_notMem hv]
    rw [this, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc_right ht.2)]
  have e2 : ∀ v, ∫ r, Ft (v, r) ∂(volume.restrict (Set.Icc l h)) =
      (Set.Icc (0 : ℝ) t).indicator (fun v => ∫ r in Set.Icc l h, Vd v r) v := by
    intro v
    by_cases hv : v ∈ Set.Icc (0 : ℝ) t
    · rw [Set.indicator_of_mem hv]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hFt, Set.indicator_of_mem (show ((v, r) : ℝ × ℝ) ∈
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv)]
    · rw [Set.indicator_of_notMem hv]
      have h0 : ∀ r, Ft (v, r) = 0 := fun r => by
        rw [hFt]
        exact Set.indicator_of_notMem (show ((v, r) : ℝ × ℝ) ∉
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv) _
      simp [h0]
  have hswap := integral_integral_swap (f := fun v r => Ft (v, r)) hFtI
  have hint : Integrable (fun r => ∫ v in Set.Icc 0 t, Vd v r) (volume.restrict (Set.Icc l h)) := by
    have := hFtI.integral_prod_right
    simpa only [e1] using this
  calc ∫ r in Set.Icc l h, Vt t r
      = ∫ r in Set.Icc l h, (V0 r + ∫ v in Set.Icc 0 t, Vd v r) := by
        refine integral_congr_ae ?_
        filter_upwards [hFTC] with r hr using hr t ht
    _ = (∫ r in Set.Icc l h, V0 r) + ∫ r in Set.Icc l h, ∫ v in Set.Icc 0 t, Vd v r :=
        integral_add hV0 hint
    _ = _ := by
        congr 1
        simp only [← e1]
        rw [← hswap]
        simp only [e2]
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (Set.Icc_subset_Icc_right ht.2)]

end HRS.MS.R26T8A

end
