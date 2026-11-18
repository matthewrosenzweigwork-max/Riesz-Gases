import HRS.MH.ScreenedDefs

/-! Packet F6 of `B:lem:screened` (S.B.4): proof of the statement of `cutoff_lipschitz` in `ScreenedSpec.lean`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem f6_lip_of_cutoff (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |f x - f y| ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)
  refine ⟨C, C.coe_nonneg, fun x y => ?_⟩
  have h := hC.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h

/-- **F6** (size S).  The cutoffs are Lipschitz (`C_c^∞`: bounded `fderiv`, `ContDiff.lipschitzWith_of_hasCompactSupport`). -/
theorem cutoff_lipschitz_proof (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ Lχ : ℝ, 0 ≤ Lχ ∧ (∀ x y, |χ x - χ y| ≤ Lχ * ‖x - y‖) ∧ (∀ x y, |χh x - χh y| ≤ Lχ * ‖x - y‖) := by
  unfold IsCutoffPair at hχ
  obtain ⟨⟨hc1, hs1, -, -, -⟩, ⟨hc2, hs2, -, -, -⟩⟩ := hχ
  obtain ⟨L1, hL1, h1⟩ := f6_lip_of_cutoff χ hc1 hs1
  obtain ⟨L2, hL2, h2⟩ := f6_lip_of_cutoff χh hc2 hs2
  refine ⟨max L1 L2, le_max_of_le_left hL1, fun x y => ?_, fun x y => ?_⟩
  · exact (h1 x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (h2 x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end HRS.MH.Screened
