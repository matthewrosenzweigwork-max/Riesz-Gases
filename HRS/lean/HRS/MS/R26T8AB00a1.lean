import HRS.MS.R26T8AB00n3

/-!
# S8.2 observed-time layer, packet T8A.B00a (helper 1): measurability of the time-zero slice

The hypotheses of B00a give joint measurability only on `[0,T] × [l,h] × Ω` with the time-zero slice null; here the slice
`V 0 · ·` is shown to be a.e. strongly measurable on `[l,h] × Ω`, by writing it as `V t₀ - ∫_0^{t₀} Vd` for a good time `t₀`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

/-- measurability of the primitive in the parameter and sample variables -/
theorem r26t8a_b00a1_prim_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (l h T t0 : ℝ) (ht0 : t0 ∈ Set.Icc 0 T) (Vd : ℝ → ℝ → Ω → ℝ)
    (hdm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => Vd p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P)) :
    AEStronglyMeasurable (fun p : ℝ × Ω => ∫ v in Set.Icc 0 t0, Vd v p.1 p.2)
      ((volume.restrict (Set.Icc l h)).prod P) := by
  have hd' := r26t8a_b00n2_assoc P _ _ Vd hdm
  have hF : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × Ω) => ({q : ℝ × (ℝ × Ω) | q.1 ∈ Set.Icc 0 t0}).indicator
        (fun q => Vd q.1 q.2.1 q.2.2) q) ((volume.restrict (Set.Icc 0 T)).prod
          ((volume.restrict (Set.Icc l h)).prod P)) :=
    hd'.indicator (measurableSet_Icc.preimage measurable_fst)
  have hint := hF.prod_swap.integral_prod_right'
  refine hint.congr (Eventually.of_forall fun y => ?_)
  have : (fun x => ({q : ℝ × (ℝ × Ω) | q.1 ∈ Set.Icc 0 t0}).indicator
        (fun q => Vd q.1 q.2.1 q.2.2) (x, y)) =
      (Set.Icc (0 : ℝ) t0).indicator (fun x => Vd x y.1 y.2) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) t0
    · rw [Set.indicator_of_mem (show ((x, y) : ℝ × (ℝ × Ω)) ∈
        {q : ℝ × (ℝ × Ω) | q.1 ∈ Set.Icc 0 t0} from hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (show ((x, y) : ℝ × (ℝ × Ω)) ∉
        {q : ℝ × (ℝ × Ω) | q.1 ∈ Set.Icc 0 t0} from hx), Set.indicator_of_notMem hx]
  simp only [Prod.swap_prod_mk, this]
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc_right ht0.2)]

theorem r26t8a_b00a1_V0_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (l h T : ℝ) (hT : 0 < T) (V Vd : ℝ → ℝ → Ω → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => V p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P))
    (hdm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => Vd p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P))
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P),
      IntegrableOn (fun v => Vd v p.1 p.2) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, V t p.1 p.2 = V 0 p.1 p.2 + ∫ v in Set.Icc 0 t, Vd v p.1 p.2) :
    AEStronglyMeasurable (fun p : ℝ × Ω => V 0 p.1 p.2)
      ((volume.restrict (Set.Icc l h)).prod P) := by
  have hm' := r26t8a_b00n2_assoc P _ _ V hm
  have hne : (volume.restrict (Set.Icc (0 : ℝ) T)) ≠ 0 := by
    intro h0
    have := congrArg (fun m : Measure ℝ => m Set.univ) h0
    simp only [Measure.restrict_apply_univ, Real.volume_Icc, Measure.coe_zero, Pi.zero_apply, sub_zero] at this
    exact (ENNReal.ofReal_pos.mpr hT).ne' this
  have : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := ae_neBot.mpr hne
  obtain ⟨t0, ht0, hslice⟩ := ((ae_restrict_mem measurableSet_Icc).and hm'.prodMk_left).exists
  have hg := r26t8a_b00a1_prim_meas P l h T t0 ht0 Vd hdm
  refine (hslice.sub hg).congr ?_
  filter_upwards [hFTC] with p hp
  simp only [Pi.sub_apply]
  rw [hp.2 t0 ht0]
  ring

end HRS.MS.R26T8A

end
