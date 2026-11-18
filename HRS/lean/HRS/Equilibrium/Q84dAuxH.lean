/-
# HRS.Equilibrium.Q84dAuxH — packet Q84d: envelope bounds and Gibbs-weighted sum bounds
-/
import HRS.Equilibrium.Q84dAuxG

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_sum_le_card (S : Finset (Fin N)) (f : Fin N → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ S, f i ≤ M) : ∑ i ∈ S, f i ≤ N * M := by
  calc ∑ i ∈ S, f i ≤ ∑ _i ∈ S, M := Finset.sum_le_sum hM
    _ = S.card * M := by simp
    _ ≤ N * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM0
      exact_mod_cast (Finset.card_le_univ S).trans (by simp)

/-- Weighted bound for ordered pair sums. -/
theorem q84d_pairSum_bound (q : ℝ) (hq : 0 ≤ q) (b : Torus d → Torus d → ℝ) (X : Config d N)
    {M : ℝ} (hM0 : 0 ≤ M) (h : ∀ i j : Fin N, i ≠ j → q * |b (X i) (X j)| ≤ M) :
    q * |pairSumOrdered b X| ≤ N * (N * M) := by
  unfold pairSumOrdered
  calc q * |∑ i, ∑ j ∈ Finset.univ.erase i, b (X i) (X j)|
      ≤ q * ∑ i, ∑ j ∈ Finset.univ.erase i, |b (X i) (X j)| := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i, q * |b (X i) (X j)| := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, (N * M) := by
        refine Finset.sum_le_sum fun i _ => q84d_sum_le_card _ _ hM0 fun j hj => ?_
        exact h i j (Finset.ne_of_mem_erase hj).symm
    _ = N * (N * M) := by simp

/-- Weighted bound for ordered triple sums. -/
theorem q84d_tripleSum_bound (q : ℝ) (hq : 0 ≤ q) (g3 : Torus d → Torus d → Torus d → ℝ)
    (X : Config d N) {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ i j k : Fin N, i ≠ j → i ≠ k → j ≠ k → q * |g3 (X i) (X j) (X k)| ≤ M) :
    q * |tripleSum g3 X| ≤ N * (N * (N * M)) := by
  unfold tripleSum
  calc q * |∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g3 (X i) (X j) (X k)|
      ≤ q * ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
          |g3 (X i) (X j) (X k)| := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
          q * |g3 (X i) (X j) (X k)| := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, (N * (N * M)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.sum_le_sum fun j hj => ?_).trans
          (q84d_sum_le_card (Finset.univ.erase i) (fun _ => (N * M)) (by positivity) fun j _ => le_rfl)
        refine q84d_sum_le_card _ _ hM0 fun k hk => ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
        have hkj : k ≠ j := Finset.ne_of_mem_erase hk
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        exact h i j k hji.symm hki.symm hkj.symm
    _ = N * (N * (N * M)) := by simp

end HRS.Q84d

end
