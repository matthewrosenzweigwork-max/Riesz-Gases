import HRS.MS.R26T8AP03a
import HRS.MS.LcEngAux2

/-!
# S8.2 local Newton layer, packet T8A.P03 (part b): z-derivatives of a convolution with a smooth compactly supported kernel
`r26t8a_stage1`: for continuous compactly supported `s` and smooth compactly supported `Kt`,
`D^q_x int Kt (x-w) s w dw = int s w . D^q Kt (x-w) dw` (merged `lc4_iteratedFDeriv_integral`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_jets_bdd {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
  have hC : ∀ i : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ C := fun i =>
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range (k + 1), max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun i hi y => ?_⟩
  have h1 : C i ≤ ∑ i ∈ Finset.range (k + 1), max (C i) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun i _ => le_max_right _ _) (Finset.mem_range.2 (by omega)))
  exact (hC i y).trans h1

theorem r26t8a_conv_jet (Kt : Euc d → ℝ) (hK : ContDiff ℝ ∞ Kt) (s : ℝ) (w : Euc d) (i : ℕ) (x : Euc d) :
    iteratedFDeriv ℝ i (fun x => s * Kt (x - w)) x = s • iteratedFDeriv ℝ i Kt (x - w) := by
  have h1 : (fun x => s * Kt (x - w)) = fun x => s • (fun z => Kt (z - w)) x := by
    funext x; simp
  have hca : ContDiffAt ℝ (i : WithTop ℕ∞) (fun z => Kt (z - w)) x :=
    ((hK.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [h1, iteratedFDeriv_const_smul_apply' hca, iteratedFDeriv_comp_sub]

theorem r26t8a_stage1 {s Kt : Euc d → ℝ} (hs : Continuous s) (hsc : HasCompactSupport s)
    (hK : ContDiff ℝ ∞ Kt) (hKc : HasCompactSupport Kt) (q : ℕ) (z : Euc d) :
    iteratedFDeriv ℝ q (fun x => ∫ w, s w * Kt (x - w)) z = ∫ w, s w • iteratedFDeriv ℝ q Kt (z - w) := by
  obtain ⟨B, hB0, hB⟩ := r26t8a_jets_bdd hK hKc q
  have hint : Integrable (fun w => ‖s w‖ * B) := ((hs.integrable_of_hasCompactSupport hsc).norm).mul_const B
  have key := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure (Euc d)))
    (fun w x => s w * Kt (x - w)) q
    (fun w => ((contDiff_const.mul (hK.comp (contDiff_id.sub contDiff_const))).of_le (by exact_mod_cast le_top)))
    (Φ := fun w => ‖s w‖ * B) hint
    (fun i hi w x => by
      rw [r26t8a_conv_jet Kt hK, norm_smul]
      exact mul_le_mul_of_nonneg_left (hB i hi _) (norm_nonneg _))
    (fun i hi x => by
      have : (fun w => iteratedFDeriv ℝ i (fun x => s w * Kt (x - w)) x) =
          fun w => s w • iteratedFDeriv ℝ i Kt (x - w) := funext fun w => r26t8a_conv_jet Kt hK _ w i x
      rw [this]
      exact (hs.smul ((hK.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable)
  rw [key.2 q le_rfl z]
  exact integral_congr_ae (Eventually.of_forall fun w => r26t8a_conv_jet Kt hK (s w) w q z)

end HRS.MS.R26T8A
