import HRS.MS.SA12X3C15E

/-!
# S.A.12 C15 (SA12X3), part F: uniform bounds of `jetSq`/`dissipSq` for a cutoff with bounded support and jets bounded by `B`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_term_bdd {w g : Euc d → ℝ} {q : Euc d} {R B : ℝ} (hw : ∀ x, |w x| ≤ 1)
    (hs : Function.support w ⊆ closedBall q R) (hg : ∀ x, |g x| ≤ B) :
    ∫ x, (w x * g x) ^ 2 ≤ B ^ 2 * (volume (closedBall q R)).toReal := by
  have hz : ∀ x ∉ closedBall q R, (w x * g x) ^ 2 = 0 := by
    intro x hx
    have : w x = 0 := by
      by_contra h; exact hx (hs (Function.mem_support.2 h))
    rw [this]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall q R) hz]
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Euc d))) (s := closedBall q R)
    (C := B ^ 2) measure_closedBall_lt_top (f := fun x => (w x * g x) ^ 2) (fun x _ => by
      rw [Real.norm_eq_abs, abs_pow, abs_mul]
      have h1 := hw x
      have h2 := hg x
      have h3 : |w x| * |g x| ≤ 1 * B := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      calc (|w x| * |g x|) ^ 2 ≤ (1 * B) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
        _ = B ^ 2 := by ring)
  refine (le_abs_self _).trans ?_
  simpa only [Real.norm_eq_abs, Measure.real] using this

theorem sa12x3_jetSq_le (m : ℕ) {w F : Euc d → ℝ} {q : Euc d} {R B : ℝ} (hw : ∀ x, |w x| ≤ 1)
    (hs : Function.support w ⊆ closedBall q R)
    (hB : ∀ j ≤ m, ∀ idx : Fin j → Fin d, ∀ x, |partialDeriv idx F x| ≤ B) :
    jetSq m w F ≤ (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
      (B ^ 2 * (volume (closedBall q R)).toReal) := by
  unfold jetSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  calc (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2
      ≤ (Nat.choose m j : ℝ) * ∑ _idx : Fin j → Fin d, B ^ 2 * (volume (closedBall q R)).toReal :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ => sa12x3_term_bdd hw hs (hB j hjm idx))
          (Nat.cast_nonneg _)
    _ = (Nat.choose m j : ℝ) * (d : ℝ) ^ j * (B ^ 2 * (volume (closedBall q R)).toReal) := by
        simp [mul_assoc]

theorem sa12x3_dissipSq_le (m : ℕ) {w F : Euc d → ℝ} {q : Euc d} {R B : ℝ} (hw : ∀ x, |w x| ≤ 1)
    (hs : Function.support w ⊆ closedBall q R)
    (hB : ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x, |partialDeriv idx F x| ≤ B) :
    dissipSq m w F ≤ (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ (j + 1)) *
      (B ^ 2 * (volume (closedBall q R)).toReal) := by
  unfold dissipSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  calc (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2
      ≤ (Nat.choose m j : ℝ) * ∑ _idx : Fin j → Fin d, ∑ _i : Fin d,
          B ^ 2 * (volume (closedBall q R)).toReal :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ => Finset.sum_le_sum fun i _ =>
          sa12x3_term_bdd hw hs (hB (j + 1) (by omega) _)) (Nat.cast_nonneg _)
    _ = (Nat.choose m j : ℝ) * (d : ℝ) ^ (j + 1) * (B ^ 2 * (volume (closedBall q R)).toReal) := by
        simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

end HRS.MH.AdjointRd.Phase2SA12Construction
