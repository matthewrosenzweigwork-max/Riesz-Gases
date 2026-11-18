import HRS.MS.SA12X2R36Q1

/-!
# S.A.12 R36 (SA12X2), part J: jet bound for products (the density `a = χ̂ μ`)

If `‖∂^j f‖ ≤ B` and `‖∂^j g‖ ≤ C` for `j ≤ k`, then `‖∂^j (f g)‖ ≤ 2^j B C` for `j ≤ k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_jet_mul_bound {k : ℕ} {f g : Euc d → ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g)
    (hfB : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hgB : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C) :
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ 2 ^ j * B * C := by
  intro j hj x
  have hLe := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hf hg x (n := j) (by exact_mod_cast hj)
  refine hLe.trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ ≤
        (j.choose i : ℝ) * B * C := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hfB i (by omega) x
    have h2 := hgB (j - i) (by omega) x
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul h1 h2 (norm_nonneg _) hB
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖
        = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖) := by ring
      _ ≤ (j.choose i : ℝ) * (B * C) := mul_le_mul_of_nonneg_left this hc
      _ = (j.choose i : ℝ) * B * C := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    have := Nat.sum_range_choose j
    exact_mod_cast this
  rw [hsum]

end HRS.MH.AdjointRd.Phase2SA12
