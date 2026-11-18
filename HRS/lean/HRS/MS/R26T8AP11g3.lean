import HRS.MS.R26T8AP08e
import HRS.MS.R26T8AP10a4

/-!
# S8.2 T8A P11g (part 3): product integrability with a pole kernel
`r26t8a_g3_prod_int`: for `a ≥ 0` continuous, bounded, integrable, `0 < e < d` and `W` integrable,
`(u, y) ↦ |W u| * (a y * (1 + ‖u - y‖^(-e)))` is integrable on `volume.prod volume`; and the swapped form.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_g3_prod_int (hd : 2 ≤ d) {e : ℝ} (he0 : 0 < e) (hed : e < d) {a : Euc d → ℝ}
    (ha0 : ∀ y, 0 ≤ a y) {Ka : ℝ} (haK : ∀ y, a y ≤ Ka) (hac : Continuous a) (hai : Integrable a)
    {W : Euc d → ℝ} (hW : Integrable W) :
    Integrable (fun p : Euc d × Euc d => |W p.1| * (a p.2 * (1 + ‖p.1 - p.2‖ ^ (-e))))
      (volume.prod volume) ∧
    Integrable (fun p : Euc d × Euc d => a p.1 * (1 + ‖p.1 - p.2‖ ^ (-e)) * |W p.2|)
      (volume.prod volume) := by
  obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd he0 hed
  set Bc : ℝ := 3 * (∫ y, a y) + Ka * Ω with hBc
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => |W p.1| * (a p.2 * (1 + ‖p.1 - p.2‖ ^ (-e))))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => |W p.1|) (volume.prod volume) :=
      hW.aestronglyMeasurable.norm.comp_fst
    have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => a p.2) (volume.prod volume) :=
      (hac.comp continuous_snd).aestronglyMeasurable
    have h3 : Measurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-e)) :=
      ((measurable_fst.sub measurable_snd).norm).pow_const _
    have h4 : AEStronglyMeasurable (fun p : Euc d × Euc d => 1 + ‖p.1 - p.2‖ ^ (-e)) (volume.prod volume) :=
      (measurable_const.add h3).aestronglyMeasurable
    exact h1.mul (h2.mul h4)
  have key : Integrable (fun p : Euc d × Euc d => |W p.1| * (a p.2 * (1 + ‖p.1 - p.2‖ ^ (-e))))
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    have hrow : ∀ u : Euc d, Integrable (fun y => |W u| * (a y * (1 + ‖u - y‖ ^ (-e)))) :=
      fun u => (hΩ a Ka ha0 haK hac hai u).1.const_mul _
    refine ⟨Filter.Eventually.of_forall hrow, ?_⟩
    have hint : ∀ u : Euc d, ∫ y, ‖|W u| * (a y * (1 + ‖u - y‖ ^ (-e)))‖ =
        |W u| * ∫ y, a y * (1 + ‖u - y‖ ^ (-e)) := by
      intro u
      rw [← integral_const_mul]
      congr 1; funext y
      have : 0 ≤ a y * (1 + ‖u - y‖ ^ (-e)) :=
        mul_nonneg (ha0 y) (by have := Real.rpow_nonneg (norm_nonneg (u - y)) (-e); linarith)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) this)]
    simp only [hint]
    refine Integrable.mono' (hW.norm.mul_const Bc) ?_ (Filter.Eventually.of_forall fun u => ?_)
    · have := (hmeas.norm).integral_prod_right'
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [hint]
    · have h0 : 0 ≤ ∫ y, a y * (1 + ‖u - y‖ ^ (-e)) :=
        integral_nonneg fun y => mul_nonneg (ha0 y)
          (by have := Real.rpow_nonneg (norm_nonneg (u - y)) (-e); linarith)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) h0)]
      exact mul_le_mul_of_nonneg_left (hΩ a Ka ha0 haK hac hai u).2 (abs_nonneg _)
  refine ⟨key, ?_⟩
  have hs := key.swap
  refine hs.congr (Filter.Eventually.of_forall fun p => ?_)
  show |W p.2| * (a p.1 * (1 + ‖p.2 - p.1‖ ^ (-e))) = _
  rw [norm_sub_rev p.2 p.1]
  ring

end HRS.MS.R26T8A
