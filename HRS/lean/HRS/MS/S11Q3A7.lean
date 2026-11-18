import HRS.MS.S11Q3A6

/-!
# S11.3 / S11.4 (worker S11Q3), A7: the integrand of the normalizer and its majorant

`s11q3_F0` (deleted-diagonal pair energy), the lower bound `F0 ≥ -N⁻¹ ∑ |X_a|`, the one-particle majorant `s11q3_h` and its integrability.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

variable {d : ℕ} {s : ℝ}

def s11q3_F0 (d : ℕ) (s : ℝ) (N : ℕ) (X : EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j)

theorem s11q3_g_lower (hs0 : 0 ≤ s) (x : Euc d) : -‖x‖ ≤ rieszKernel d s x := by
  unfold rieszKernel
  split_ifs with h
  · have := Real.log_le_self (norm_nonneg x)
    linarith
  · have := Real.rpow_nonneg (norm_nonneg x) (-s)
    linarith [norm_nonneg x]

theorem s11q3_F0_lower (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) (X : EucConfig d N) :
    -((1 / (N : ℝ)) * ∑ a, ‖X a‖) ≤ s11q3_F0 d s N X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set T : ℝ := ∑ a, ‖X a‖ with hT
  have h1 : ∀ i j, -(‖X i‖ + ‖X j‖) ≤ rieszKernel d s (X i - X j) := fun i j =>
    (neg_le_neg (norm_sub_le _ _)).trans (s11q3_g_lower hs0 _)
  have h3 : ∀ i, ∑ j ∈ Finset.univ.erase i, (‖X i‖ + ‖X j‖) ≤ ∑ j, (‖X i‖ + ‖X j‖) := fun i =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _) (fun j _ _ => by positivity)
  have h4 : ∑ i, ∑ j, (‖X i‖ + ‖X j‖) = 2 * N * T := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hT, ← Finset.mul_sum]
    ring
  have h5 : -(2 * N * T) ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j) := by
    calc -(2 * N * T) = -(∑ i, ∑ j, (‖X i‖ + ‖X j‖)) := by rw [h4]
      _ ≤ -(∑ i, ∑ j ∈ Finset.univ.erase i, (‖X i‖ + ‖X j‖)) :=
          neg_le_neg (Finset.sum_le_sum fun i _ => h3 i)
      _ ≤ _ := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_le_sum fun j _ => h1 i j
  unfold s11q3_F0
  have h6 : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  calc -((1 / (N : ℝ)) * T) = (1 / (2 * (N : ℝ) ^ 2)) * (-(2 * N * T)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 h6

end HRS.MS.S11Q3

end
