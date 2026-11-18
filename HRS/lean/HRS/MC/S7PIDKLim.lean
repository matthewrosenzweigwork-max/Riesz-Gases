import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet K (part 5): the limit of a geometrically Cauchy sequence in `projTensor`
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDK_rpow_quarter (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ) / 4) = ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

set_option maxSynthPendingDepth 3 in
theorem S7PIDK_limit {m T : ℝ} (τ : ℕ → TensorDual (PathSpace d m T) 2)
    (hmem : ∀ n, τ n ∈ projTensor (PathSpace d m T) 2) (W : ℝ) (hW : 0 ≤ W)
    (hd : ∀ n, ‖τ (n + 1) - τ n‖ ≤ W * (2 : ℝ) ^ (-(n : ℝ) / 4)) (hb : ∀ n, ‖τ n‖ ≤ W) :
    ∃ τ' : TensorDual (PathSpace d m T) 2, τ' ∈ projTensor (PathSpace d m T) 2 ∧
      Tendsto τ atTop (𝓝 τ') ∧ ‖τ'‖ ≤ W := by
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hr1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum : Summable fun n : ℕ => dist (τ n) (τ (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left W)
    rw [dist_eq_norm, norm_sub_rev, ← S7PIDK_rpow_quarter]
    exact hd n
  obtain ⟨τ', hτ'⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  refine ⟨τ', ?_, hτ', ?_⟩
  · have hcl : IsClosed (projTensor (PathSpace d m T) 2 : Set (TensorDual (PathSpace d m T) 2)) := by
      unfold projTensor
      exact Submodule.isClosed_topologicalClosure _
    exact hcl.mem_of_tendsto hτ' (Filter.Eventually.of_forall hmem)
  · exact le_of_tendsto' hτ'.norm hb

end HRS.MC.Sec7.S7PIDK

end
