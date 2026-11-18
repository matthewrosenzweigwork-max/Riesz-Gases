import HRS.MS.R26T8AA01f

/-!
# S8.2 T8A A01 (part g): principal-value truncation of an odd kernel
For `κ` odd, measurable, bounded away from `0`, and `φ` with integrable canonical integrand at `u`:
`∫_{ε < ‖u-z‖, ε < ‖v-z‖} φ(z) κ(u-z) dz → ∫ (if ‖u-z‖ ≤ 1/4 then (φ z - φ u) κ(u-z) else φ z κ(u-z)) dz` as `ε → 0+`
(`v ≠ u` a second point at which `φ κ(u-·)` is locally integrable).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_a01_pv {u v : Euc d} (huv : u ≠ v) {κ : Euc d → ℝ} (hκm : Measurable κ)
    (hodd : ∀ w, κ (-w) = -κ w) (hκb : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ w : Euc d, δ ≤ ‖w‖ → |κ w| ≤ B)
    {φ : Euc d → ℝ} (hφm : AEStronglyMeasurable φ volume)
    (hI : Integrable (fun z => if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * κ (u - z) else φ z * κ (u - z)))
    {r : ℝ} (hr : 0 < r) (hv : IntegrableOn (fun z => φ z * κ (u - z)) (ball v r)) :
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => φ z * κ (u - z)) z) (𝓝[>] 0)
      (𝓝 (∫ z, if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * κ (u - z) else φ z * κ (u - z))) := by
  set f : Euc d → ℝ := fun z => φ z * κ (u - z) with hf
  set Fc : Euc d → ℝ := fun z => if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * κ (u - z) else φ z * κ (u - z) with hFc
  haveI : Nontrivial (Euc d) := ⟨⟨u, v, huv⟩⟩
  have huvn : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
  have hfm : AEStronglyMeasurable f volume :=
    hφm.mul ((hκm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hae : ∀ᵐ z : Euc d ∂volume, z ≠ u := compl_mem_ae_iff.mpr (measure_singleton u)
  have hae' : ∀ᵐ z : Euc d ∂volume, z ≠ v := compl_mem_ae_iff.mpr (measure_singleton v)
  -- the integrable annulus piece
  have hann : ∀ ε : ℝ, 0 < ε → Integrable (fun z : Euc d => if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) := by
    intro ε hε
    obtain ⟨B, hB⟩ := hκb ε hε
    have hm : Measurable (fun z : Euc d => if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) := by
      refine Measurable.ite ?_ (hκm.comp (measurable_const.sub measurable_id)) measurable_const
      exact (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
        (measurableSet_le (measurable_const.sub measurable_id).norm measurable_const)
    refine Integrable.mono' (g := fun z => (closedBall u (1 / 4)).indicator (fun _ => |B|) z)
      ?_ hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const (by exact measure_closedBall_lt_top.ne))
    · by_cases h : ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4
      · rw [if_pos h, Real.norm_eq_abs]
        have hz : z ∈ closedBall u (1 / 4) := by
          rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact h.2
        rw [Set.indicator_of_mem hz]
        exact (hB _ h.1.le).trans (le_abs_self B)
      · rw [if_neg h]; simp only [norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) z
  have hannz : ∀ ε : ℝ, 0 < ε → ∫ z : Euc d, (if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) = 0 := by
    intro ε hε
    obtain ⟨B, hB⟩ := hκb ε hε
    exact r26t8a_a01_annulus_zero hκm hodd u hε ⟨B, hB⟩
  -- the pieces and their limits
  have t1 : Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖} Fc z) (𝓝[>] 0) (𝓝 (∫ z, Fc z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖Fc z‖) ?_ ?_ hI.norm ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      have hs : MeasurableSet {z : Euc d | ε < ‖u - z‖} :=
        measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
      exact hI.aestronglyMeasurable.indicator hs
    · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun z => ?_
      by_cases h : ε < ‖u - z‖
      · rw [Set.indicator_of_mem (show z ∈ {z : Euc d | ε < ‖u - z‖} from h)]
      · rw [Set.indicator_of_notMem (show z ∉ {z : Euc d | ε < ‖u - z‖} from h)]; simp
    · filter_upwards [hae] with z hz
      have hn : 0 < ‖u - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.symm)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
      rw [Set.indicator_of_mem (show z ∈ {z : Euc d | ε < ‖u - z‖} from hε.2)]
  have t2 : Tendsto (fun ε : ℝ => ∫ z, Set.indicator (closedBall v ε) f z) (𝓝[>] 0) (𝓝 0) := by
    have hvi : Integrable (fun z => (ball v r).indicator f z) :=
      (integrable_indicator_iff measurableSet_ball).2 hv
    have := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (F := fun ε z => Set.indicator (closedBall v ε) f z) (f := fun _ => (0 : ℝ))
      (fun z => ‖(ball v r).indicator f z‖) ?_ ?_ hvi.norm ?_
    · simpa using this
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact hfm.indicator measurableSet_closedBall
    · filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases h : z ∈ closedBall v ε
      · rw [Set.indicator_of_mem h]
        have : z ∈ ball v r := by
          rw [mem_ball]; rw [mem_closedBall] at h; linarith [hε.2]
        rw [Set.indicator_of_mem this]
      · rw [Set.indicator_of_notMem h]; simp
    · filter_upwards [hae'] with z hz
      have hn : 0 < dist z v := dist_pos.2 hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
      rw [Set.indicator_of_notMem (show z ∉ closedBall v ε by rw [mem_closedBall]; exact not_le.2 hε.2)]
  have t3 := t1.sub t2
  rw [sub_zero] at t3
  refine t3.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (min (1 / 4) r) (‖u - v‖ / 2) by positivity)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hε2 : ε < ‖u - v‖ / 2 := lt_of_lt_of_le hε1 (min_le_right _ _)
  have hεr : ε < r := lt_of_lt_of_le hε1 ((min_le_left _ _).trans (min_le_right _ _))
  -- pointwise decomposition
  have hid : ∀ z : Euc d, ε < ‖u - z‖ → Fc z + φ u * (if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) = f z := by
    intro z hz
    by_cases h14 : ‖u - z‖ ≤ 1 / 4
    · simp only [hFc, hf, if_pos h14, if_pos (show ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 from ⟨hz, h14⟩)]; ring
    · simp only [hFc, hf, if_neg h14, if_neg (show ¬ (ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4) from fun h => h14 h.2)]; ring
  have hpt : ∀ z : Euc d, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} f z =
      Set.indicator {z : Euc d | ε < ‖u - z‖} Fc z -
        Set.indicator (closedBall v ε) f z +
        φ u * (if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) := by
    intro z
    by_cases hA : ε < ‖u - z‖
    · have hid' := hid z hA
      rw [Set.indicator_of_mem (show z ∈ {z : Euc d | ε < ‖u - z‖} from hA)]
      by_cases hv' : ε < ‖v - z‖
      · rw [Set.indicator_of_mem (show z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} from ⟨hA, hv'⟩),
          Set.indicator_of_notMem (show z ∉ closedBall v ε by
            rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact not_le.2 hv')]
        linarith
      · rw [Set.indicator_of_notMem (show z ∉ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} from fun h => hv' h.2),
          Set.indicator_of_mem (show z ∈ closedBall v ε by
            rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact not_lt.1 hv')]
        linarith
    · rw [Set.indicator_of_notMem (show z ∉ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} from fun h => hA h.1),
        Set.indicator_of_notMem (show z ∉ {z : Euc d | ε < ‖u - z‖} from hA),
        Set.indicator_of_notMem (show z ∉ closedBall v ε by
          rw [mem_closedBall, dist_eq_norm]
          intro hcb
          have h1 : ‖u - v‖ ≤ ‖u - z‖ + ‖z - v‖ := norm_sub_le_norm_sub_add_norm_sub u z v
          have h2 : ‖u - z‖ ≤ ε := not_lt.1 hA
          linarith),
        if_neg (show ¬ (ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4) from fun h => hA h.1)]
      simp
  have hsA : MeasurableSet {z : Euc d | ε < ‖u - z‖} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
  have i1 : Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖} Fc) := hI.indicator hsA
  have i2 : Integrable (Set.indicator (closedBall v ε) f) :=
    (hv.mono_set (closedBall_subset_ball hεr)).integrable_indicator measurableSet_closedBall
  have i3 : Integrable (fun z : Euc d => φ u * (if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0)) :=
    (hann ε hε0).const_mul _
  have i12 : Integrable (fun z : Euc d => Set.indicator {z : Euc d | ε < ‖u - z‖} Fc z -
      Set.indicator (closedBall v ε) f z) := i1.sub i2
  simp only [hpt]
  rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul, hannz ε hε0, mul_zero, add_zero]

end HRS.MS.R26T8A
