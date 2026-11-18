import HRS.MS.SA12X3C9A

/-!
# S.A.12 C9 (SA12X3), part B: the transport commutator (the Leibniz remainder of `⟨b,∇F⟩`)
`sa12z3_Rj_pt` with the bound on `a` only for derivatives of order `≥ 1` (the drift is unbounded).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3_Rj_pt' {m n : ℕ} (hn : n ≤ m) {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a)
    (hF : ContDiff ℝ ∞ F) {Ka : ℝ} (hKa : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka)
    (idx : Fin n → Fin d) (j : Fin d) (y : Euc d) :
    |sa12z3_Rj a F idx j y| ≤ Ka * 2 ^ m * sa12z3_T m F y := by
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa 1 le_rfl (by omega) y)
  have hDF : ContDiff ℝ n (D1 j F) :=
    ((sa12z3_cd_of_inf hF (n + 1)).fderiv_right (m := n) (by push_cast; rfl)).clm_apply contDiff_const
  have han : ContDiff ℝ n a := ha.of_le (by exact_mod_cast (by omega : n ≤ m + 1))
  have h1 := sa12z3_leib_diff han hDF idx y
  have hcomm : D1 j (partialDeriv idx F) y = partialDeriv idx (D1 j F) y :=
    (sa12z3_pd_D1_comm j n F (sa12z3_cd_of_inf hF _) idx y).symm
  have e : sa12z3_Rj a F idx j y =
      partialDeriv idx (fun y => a y * D1 j F y) y - a y * partialDeriv idx (D1 j F) y := by
    unfold sa12z3_Rj; rw [hcomm]
  rw [e]
  refine h1.trans ?_
  have hT0 := sa12z3_T_nonneg m F y
  have hterm : ∀ k ∈ Finset.range (n + 1), (if k = 0 then (0 : ℝ) else
      (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k a y‖ * ‖iteratedFDeriv ℝ (n - k) (D1 j F) y‖) ≤
      (n.choose k : ℝ) * (Ka * sa12z3_T m F y) := by
    intro k hk
    by_cases hk0 : k = 0
    · rw [if_pos hk0]; positivity
    · rw [if_neg hk0]
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hka := hKa k (by omega) (by omega) y
      have hnorm : ‖iteratedFDeriv ℝ (n - k) (D1 j F) y‖ ≤ sa12z3_T m F y :=
        (sa12z3_norm_iter_le _ y (n - k)).trans (sa12z3_sum_pd_D1_le_T (by omega) hF j y)
      calc (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k a y‖ * ‖iteratedFDeriv ℝ (n - k) (D1 j F) y‖
          ≤ (n.choose k : ℝ) * Ka * sa12z3_T m F y := by gcongr
        _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (Ka * sa12z3_T m F y) =
      2 ^ n * (Ka * sa12z3_T m F y) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose n
  rw [hsum]
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hn
  calc (2 : ℝ) ^ n * (Ka * sa12z3_T m F y) ≤ 2 ^ m * (Ka * sa12z3_T m F y) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
