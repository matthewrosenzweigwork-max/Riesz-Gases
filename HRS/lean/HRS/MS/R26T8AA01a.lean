import HRS.MS.R26T8AA00
import HRS.MS.R2InterpAux7

/-!
# S8.2 T8A A01 (part a): the pointwise envelope of `tripleG`
For `Q` a `PairCorrector` and `‖forceMean ρ‖ ≤ BF`: on pairwise distinct `x y z`,
`|tripleG x y z| ≤ K (1+BF) A jb(x)^M' jb(y)^M' jb(z)^M' triplePole x y z`.
The three singular force pairs are grouped (`g(x-z)` with `g(z-x)`, etc.) and A00 is applied to each group.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_pole_comm (x y : Euc d) : pole x y = pole y x := by
  unfold pole smallRadius; rw [norm_sub_rev]

theorem r26t8a_a01_pole_ge_one (x y : Euc d) : 1 ≤ pole x y := by
  unfold pole
  have := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg (x - y))) (-criticalS d)
  unfold smallRadius; linarith

theorem r26t8a_a01_pole_ge (hs : 0 < criticalS d) {x z : Euc d} (hxz : x ≠ z) :
    ‖x - z‖ ^ (-criticalS d) ≤ pole x z := by
  have hn : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  unfold pole smallRadius
  by_cases h : 1 ≤ ‖x - z‖
  · rw [min_eq_left h, Real.one_rpow]
    have : ‖x - z‖ ^ (-criticalS d) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    linarith
  · push Not at h
    rw [min_eq_right h.le]; linarith

theorem r26t8a_a01_grad_pole {x y : Euc d} (hxy : x ≠ y) (hs : 1 ≤ criticalS d) :
    1 + smallRadius x y ^ (1 - criticalS d) ≤ pole x y := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold pole smallRadius
  have h0 : 0 < min 1 ‖x - y‖ := lt_min zero_lt_one hn
  have h1 : min 1 ‖x - y‖ ≤ 1 := min_le_left _ _
  have e : min 1 ‖x - y‖ ^ (1 - criticalS d) = min 1 ‖x - y‖ * min 1 ‖x - y‖ ^ (-criticalS d) := by
    rw [show (1 - criticalS d) = 1 + (-criticalS d) by ring, Real.rpow_add h0, Real.rpow_one]
  have hnn : 0 ≤ min 1 ‖x - y‖ ^ (-criticalS d) := Real.rpow_nonneg h0.le _
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right h1 hnn]

end HRS.MS.R26T8A
