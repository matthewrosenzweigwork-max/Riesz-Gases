import HRS.MS.R26T8AP11g8
import HRS.MS.R26T8AP11g2

/-!
# S8.2 T8A P11g (part 9): integration by parts of a conormal function against a compactly supported field
For `w` `C^1` with compact support and `Q` conormal (pole order `σ-2 < d-1`):
`∫ ∑_j w_j ∂_jQ(·,y) = - ∫ Q(·,y) div w`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_g9_gauss_compact {V : Type*} [NormedAddCommGroup V] {f : Euc d → V} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ D : ℝ, 0 ≤ D ∧ ∀ u, ‖f u‖ ≤ D * Real.exp (-1 * ‖u‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * Real.exp (R ^ 2), by positivity, fun u => ?_⟩
  by_cases hu : u ∈ Function.support f
  · have h1 : ‖u‖ ≤ R := by simpa using hR (subset_tsupport f hu)
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
    have h2 : Real.exp (R ^ 2) * Real.exp (-1 * ‖u‖ ^ 2) ≥ 1 := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [norm_nonneg u])
    calc ‖f u‖ ≤ C := hC u
      _ = C * 1 := (mul_one _).symm
      _ ≤ C * (Real.exp (R ^ 2) * Real.exp (-1 * ‖u‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 hC0
      _ = _ := by ring
  · have : f u = 0 := by simpa using hu
    rw [this, norm_zero]
    have := Real.exp_pos (-1 * ‖u‖ ^ 2)
    positivity

end HRS.MS.R26T8A
