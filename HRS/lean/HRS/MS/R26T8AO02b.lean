import HRS.MS.R26T8AO02a

/-!
# S8.2 T8A O02 (part b): the `A`-free envelope functions are tame
`Wb`, `Pj`, `Tr` dominate the pointwise bounds of the pair statistics, the repeated pair terms and the triple sum;
their sum is dominated by a pole envelope `u4Env p q`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W

variable {d N : ℕ}

def r26t8a_o02_Wb (M : ℝ) (X : EucConfig d N) : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M 1 i j X

def r26t8a_o02_Pj (M' : ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, HRS.MS.Phase2S82.pairWeight M' (X i) (X j) * pole (X i) (X j) ^ 2

def r26t8a_o02_Tr (M' : ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
    (jbracket (X i) ^ M' * jbracket (X j) ^ M' * jbracket (X k) ^ M') * triplePole (X i) (X j) (X k)

theorem r26t8a_o02_jb_le {M : ℝ} (hM : 0 ≤ M) (X : EucConfig d N) (k : Fin N) :
    jbracket (X k) ^ M ≤ (1 + ‖X‖) ^ M :=
  Real.rpow_le_rpow (Real.sqrt_nonneg _) ((w_jb_le (X k)).trans (by linarith [norm_le_pi_norm X k])) hM

theorem r26t8a_o02_pole_le (X : EucConfig d N) (i j : Fin N) :
    pole (X i) (X j) ≤ 2 + ‖X i - X j‖ ^ (-criticalS d) := by
  unfold pole smallRadius
  rcases le_total 1 ‖X i - X j‖ with h | h
  · rw [min_eq_left h, Real.one_rpow]
    linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-criticalS d)]
  · rw [min_eq_right h]; linarith

theorem r26t8a_o02_pole_nonneg (x y : Euc d) : 0 ≤ pole x y := by
  linarith [r26t8a_a01_pole_ge_one x y]

end HRS.MS.R26T8A
