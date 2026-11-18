import HRS.MS.SA12X2R34A

/-!
# S.A.12 R34 (SA12X2), part B: pointwise Leibniz bound for the iterated derivative of `a * F`

If `‖∂^i a‖ ≤ B` for `i ≤ m+1`, then for `j ≤ m+1`:
`‖∂^j (a F)(x)‖² ≤ B² (2^j)² (j+1) ∑_{i ≤ j} ‖∂^{j-i} F(x)‖²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_leib_pt {m : ℕ} {B : ℝ} (hB0 : 0 ≤ B) {a F : Euc d → ℝ}
    (ha : ContDiff ℝ (m + 1) a) (hF : ContDiff ℝ (m + 1) F)
    (hB : ∀ i ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ B) {j : ℕ} (hj : j ≤ m + 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ^ 2 ≤
      B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) *
        ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 := by
  have hLe := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) ha hF x (n := j) (by exact_mod_cast hj)
  have hbound : ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ≤
      B * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j - i) F x‖ := by
    refine hLe.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hB i (by omega) x
    have hC : 0 ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j - i) F x‖ := by positivity
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (j - i) F x‖
        = ‖iteratedFDeriv ℝ i a x‖ * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j - i) F x‖) := by ring
      _ ≤ B * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j - i) F x‖) :=
          mul_le_mul_of_nonneg_right h1 hC
  have hQ : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j - i) F x‖ ≤
      (2 : ℝ) ^ j * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : (j.choose i : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_two_pow j i
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hCS : (∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖) ^ 2 ≤
      ((j : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun i => ‖iteratedFDeriv ℝ (j - i) F x‖)
    rw [Finset.card_range] at this
    push_cast at this
    exact this
  have hA : ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ≤
      B * ((2 : ℝ) ^ j * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖) :=
    hbound.trans (mul_le_mul_of_nonneg_left hQ hB0)
  have hA2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  calc ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ^ 2
      ≤ (B * ((2 : ℝ) ^ j * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖)) ^ 2 := hA2
    _ = B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * (∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖) ^ 2 := by
        ring
    _ ≤ B ^ 2 * ((2 : ℝ) ^ j) ^ 2 *
          (((j : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2) := by
        gcongr
    _ = B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) *
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 := by ring

end HRS.MH.AdjointRd.Phase2SA12
