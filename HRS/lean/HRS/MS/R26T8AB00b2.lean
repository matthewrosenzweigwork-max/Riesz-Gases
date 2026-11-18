import HRS.MS.R26T8AB00b1

/-!
# S8.2 observed-time layer, packet T8A.B00b (helper 2): sample-wise bound and Fubini transfer on the triangle

For a fixed sample (functions `D r = V r r`, `Vt t r`, `Vd v r`), with the clipped derivative `clip v r = if r ≤ v then Vd v r else 0`:
the bound `‖∫_0^t Vt t r dr‖ₑ ≤ ∫⁻‖D‖ₑ + ∫⁻∫⁻‖clip‖ₑ` (`r26t8a_b00b2_pt`) and the anchored primitive form
`∫_0^t Vt t r dr = ∫_0^t (D s + ∫_ν clip s r dr) ds` (`r26t8a_b00b2_fubini`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00b2_pt (T : ℝ) (D : ℝ → ℝ) (Vt Vd : ℝ → ℝ → ℝ)
    (hD : AEMeasurable (fun r => ‖D r‖ₑ) (volume.restrict (Set.Icc 0 T)))
    (hFTC : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)),
      ∀ t ∈ Set.Icc r T, Vt t r = D r + ∫ v in Set.Icc r t, Vd v r)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖∫ r in Set.Icc 0 t, Vt t r‖ₑ ≤ (∫⁻ r in Set.Icc 0 T, ‖D r‖ₑ) +
      ∫⁻ r in Set.Icc 0 T, ∫⁻ v in Set.Icc 0 T, ‖if r ≤ v then Vd v r else 0‖ₑ := by
  have hsub : Set.Icc 0 t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc_right ht.2
  have hae := ae_restrict_of_ae_restrict_of_subset hsub hFTC
  calc ‖∫ r in Set.Icc 0 t, Vt t r‖ₑ ≤ ∫⁻ r in Set.Icc 0 t, ‖Vt t r‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Set.Icc 0 t, (‖D r‖ₑ + ∫⁻ v in Set.Icc 0 T, ‖if r ≤ v then Vd v r else 0‖ₑ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with r hr hrm
        rw [hr t ⟨hrm.2, ht.2⟩]
        refine (enorm_add_le _ _).trans (add_le_add_right ?_ _)
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        calc ∫⁻ v in Set.Icc r t, ‖Vd v r‖ₑ
            = ∫⁻ v in Set.Icc r t, ‖if r ≤ v then Vd v r else 0‖ₑ := by
              refine setLIntegral_congr_fun measurableSet_Icc fun v hv => ?_
              rw [if_pos hv.1]
          _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc hrm.1 ht.2)
    _ ≤ ∫⁻ r in Set.Icc 0 T, (‖D r‖ₑ + ∫⁻ v in Set.Icc 0 T, ‖if r ≤ v then Vd v r else 0‖ₑ) :=
        lintegral_mono_set hsub
    _ = _ := lintegral_add_left' hD _

theorem r26t8a_b00b2_fubini (T : ℝ) (D : ℝ → ℝ) (Vt Vd : ℝ → ℝ → ℝ)
    (hD : Integrable D (volume.restrict (Set.Icc 0 T)))
    (hI : Integrable (fun q : ℝ × ℝ => if q.2 ≤ q.1 then Vd q.1 q.2 else 0)
      ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))))
    (hFTC : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)),
      ∀ t ∈ Set.Icc r T, Vt t r = D r + ∫ v in Set.Icc r t, Vd v r) :
    IntegrableOn (fun s => D s + ∫ r in Set.Icc 0 T, (if r ≤ s then Vd s r else 0))
        (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ∫ r in Set.Icc 0 t, Vt t r =
        ∫ s in Set.Icc 0 t, (D s + ∫ r in Set.Icc 0 T, (if r ≤ s then Vd s r else 0)) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hEint : Integrable (fun s => ∫ r, (if r ≤ s then Vd s r else 0) ∂μT) μT :=
    hI.integral_prod_left
  refine ⟨hD.add hEint, fun t ht => ?_⟩
  have hsub : Set.Icc 0 t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc_right ht.2
  set Ft : ℝ × ℝ → ℝ := fun q => ({q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t}).indicator
    (fun q => if q.2 ≤ q.1 then Vd q.1 q.2 else 0) q with hFt
  have hFtI : Integrable Ft (μT.prod μT) := hI.indicator (measurableSet_Icc.preimage measurable_fst)
  have e1 : ∀ r, ∫ v, Ft (v, r) ∂μT = ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0) := by
    intro r
    have : (fun v => Ft (v, r)) =
        (Set.Icc (0 : ℝ) t).indicator (fun v => if r ≤ v then Vd v r else 0) := by
      funext v
      by_cases hv : v ∈ Set.Icc (0 : ℝ) t
      · rw [hFt]; simp only [Set.indicator_of_mem (show ((v, r) : ℝ × ℝ) ∈
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv), Set.indicator_of_mem hv]
      · rw [hFt]; simp only [Set.indicator_of_notMem (show ((v, r) : ℝ × ℝ) ∉
          {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 t} from hv), Set.indicator_of_notMem hv]
    rw [this, integral_indicator measurableSet_Icc, hμT, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr hsub]
  have e2 : ∀ v, ∫ r, Ft (v, r) ∂μT =
      (Set.Icc (0 : ℝ) t).indicator (fun v => ∫ r, (if r ≤ v then Vd v r else 0) ∂μT) v := by
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
  have hHint : Integrable (fun r => ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) μT := by
    have := hFtI.integral_prod_right
    simpa only [e1] using this
  have hae0 : ∀ᵐ r ∂μT, r ∈ Set.Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  have hae := ae_restrict_of_ae_restrict_of_subset hsub hFTC
  -- first step: peel off the primitive
  have step1 : ∫ r in Set.Icc 0 t, Vt t r =
      (∫ r in Set.Icc 0 t, D r) +
        ∫ r in Set.Icc 0 t, ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0) := by
    rw [← integral_add (hD.mono_measure (Measure.restrict_mono hsub le_rfl))
      (hHint.mono_measure (Measure.restrict_mono hsub le_rfl))]
    refine integral_congr_ae ?_
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with r hr hrm
    rw [hr t ⟨hrm.2, ht.2⟩, r26t8a_b00b1_clip_int (fun v => Vd v r) r t hrm.1]
  -- the second term is the full integral over `μT` (it vanishes for `r > t`)
  have step2 : ∫ r in Set.Icc 0 t, ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0) =
      ∫ r, (∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) ∂μT := by
    have hres : ∀ f : ℝ → ℝ, ∫ r in Set.Icc 0 t, f r = ∫ r in Set.Icc 0 t, f r ∂μT := fun f => by
      rw [hμT, Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.mpr hsub]
    rw [hres (fun r => ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0))]
    have key : ∀ᵐ r ∂μT, r ∉ Set.Icc (0 : ℝ) t →
        (∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) = 0 := by
      filter_upwards [hae0] with r hr hrn
      have hrt : t < r := by
        by_contra hc
        exact hrn ⟨hr.1, not_lt.1 hc⟩
      refine integral_eq_zero_of_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
      simp only [Pi.zero_apply]
      rw [if_neg (not_le.2 (lt_of_le_of_lt hv.2 hrt))]
    exact setIntegral_eq_integral_of_ae_compl_eq_zero
      (f := fun r => ∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) key
  have step3 : ∫ r, (∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) ∂μT =
      ∫ v in Set.Icc 0 t, ∫ r, (if r ≤ v then Vd v r else 0) ∂μT := by
    calc ∫ r, (∫ v in Set.Icc 0 t, (if r ≤ v then Vd v r else 0)) ∂μT
        = ∫ r, (∫ v, Ft (v, r) ∂μT) ∂μT :=
          integral_congr_ae (Eventually.of_forall fun r => (e1 r).symm)
      _ = ∫ v, (∫ r, Ft (v, r) ∂μT) ∂μT := hswap.symm
      _ = ∫ v, (Set.Icc (0 : ℝ) t).indicator (fun v => ∫ r, (if r ≤ v then Vd v r else 0) ∂μT) v ∂μT :=
          integral_congr_ae (Eventually.of_forall e2)
      _ = _ := by
          rw [integral_indicator measurableSet_Icc, hμT, Measure.restrict_restrict measurableSet_Icc,
            Set.inter_eq_left.mpr hsub]
  rw [step1, step2, step3, integral_add (hD.mono_measure (Measure.restrict_mono hsub le_rfl))
    (hEint.mono_measure (Measure.restrict_mono hsub le_rfl))]

end HRS.MS.R26T8A

end
