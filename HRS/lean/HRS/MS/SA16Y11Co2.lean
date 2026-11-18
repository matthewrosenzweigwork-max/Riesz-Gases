import HRS.MS.SA16Y11Co1

/-!
# S.A.16 (SA16Y11) Co2: `IsRegularDensityW` is monotone in the order (`m+2`-level data give the `m+3`-level regularity used by Nl2/Kd/Src)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Co2
variable {d : ℕ}

lemma sa16y11_regDensity_mono {r r' : ℕ} (hr : r' ≤ r) {Λ : ℝ} {ρ : Euc d → ℝ} (h : IsRegularDensityW r Λ ρ) :
    IsRegularDensityW r' Λ ρ := by
  obtain ⟨hC, hcb, hsum⟩ := h
  refine ⟨hC.of_le (by exact_mod_cast hr), ⟨hcb.1.of_le (by exact_mod_cast hr), fun j hj => hcb.2 j (hj.trans hr)⟩, ?_⟩
  refine le_trans (add_le_add ?_ ?_) hsum
  · refine ENNReal.ofReal_le_ofReal ?_
    unfold HRS.cbNorm
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) fun j _ _ => ?_
    exact Real.iSup_nonneg fun x => norm_nonneg _
  · unfold weightedSupE derivSupE
    refine iSup_le fun j => ?_
    exact le_iSup_of_le ⟨j.val, by omega⟩ le_rfl

end Co2

end HRS.Whole.AppendixA.Phase2SA16R

end
