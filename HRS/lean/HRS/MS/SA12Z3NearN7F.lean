import HRS.MS.SA12Z3NearN7E

/-!
# S.A.12 N7 (SA12Z3), part F: the jet sums `T`, `Y` and the pointwise bound of the Leibniz remainder
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `T(y) = ∑_{r ≤ m} ∑_γ |∂^γ F(y)|`. -/
def sa12z3_T (m : ℕ) (F : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), ∑ γ : Fin r → Fin d, |partialDeriv γ F y|

/-- `Y(y) = ∑_{r ≤ m} ∑_γ (∂^γ F(y))²`. -/
def sa12z3_Y (m : ℕ) (F : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∑ r ∈ Finset.range (m + 1), ∑ γ : Fin r → Fin d, partialDeriv γ F y ^ 2

/-- The number of jets. -/
def sa12z3_cT (d m : ℕ) : ℝ := ∑ r ∈ Finset.range (m + 1), (d : ℝ) ^ r

theorem sa12z3_T_nonneg (m : ℕ) (F : Euc d → ℝ) (y : Euc d) : 0 ≤ sa12z3_T m F y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sa12z3_Y_nonneg (m : ℕ) (F : Euc d → ℝ) (y : Euc d) : 0 ≤ sa12z3_Y m F y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sa12z3_cT_nonneg (d m : ℕ) : 0 ≤ sa12z3_cT d m :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sa12z3_T_sq (m : ℕ) (F : Euc d → ℝ) (y : Euc d) :
    sa12z3_T m F y ^ 2 ≤ sa12z3_cT d m * sa12z3_Y m F y := by
  unfold sa12z3_T sa12z3_Y sa12z3_cT
  rw [Finset.sum_sigma', Finset.sum_sigma']
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.range (m + 1)).sigma
    (fun r => (Finset.univ : Finset (Fin r → Fin d)))) (f := fun p => |partialDeriv p.2 F y|)
  have hc : (((Finset.range (m + 1)).sigma
      (fun r => (Finset.univ : Finset (Fin r → Fin d)))).card : ℝ) = ∑ r ∈ Finset.range (m + 1), (d : ℝ) ^ r := by
    rw [Finset.card_sigma]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    simp
  rw [hc] at h
  simpa [sq_abs] using h

theorem sa12z3_pd_sq_le_Y {m r : ℕ} (hr : r ≤ m) (F : Euc d → ℝ) (y : Euc d) (γ : Fin r → Fin d) :
    partialDeriv γ F y ^ 2 ≤ sa12z3_Y m F y := by
  unfold sa12z3_Y
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ γ : Fin r → Fin d, partialDeriv γ F y ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
  exact Finset.single_le_sum (f := fun γ : Fin r → Fin d => partialDeriv γ F y ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ γ)

theorem sa12z3_sum_pd_le_T {m r : ℕ} (hr : r ≤ m) (F : Euc d → ℝ) (y : Euc d) :
    ∑ γ : Fin r → Fin d, |partialDeriv γ F y| ≤ sa12z3_T m F y := by
  unfold sa12z3_T
  exact Finset.single_le_sum (f := fun r => ∑ γ : Fin r → Fin d, |partialDeriv γ F y|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hr))

/-- Jets of `∂_j F` are jets of `F`. -/
theorem sa12z3_sum_pd_D1_le_T {m l : ℕ} (hl : l + 1 ≤ m) {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (j : Fin d) (y : Euc d) :
    ∑ γ : Fin l → Fin d, |partialDeriv γ (D1 j F) y| ≤ sa12z3_T m F y := by
  have h1 : ∀ γ : Fin l → Fin d, |partialDeriv γ (D1 j F) y| =
      |partialDeriv (Fin.cons j γ : Fin (l + 1) → Fin d) F y| := by
    intro γ
    rw [sa12z3_pd_D1_comm j l F (sa12z3_cd_of_inf hF _) γ y,
      sa12z3_pd_cons γ j (sa12z3_cd_of_inf hF _) y]
  simp_rw [h1]
  have hinj : Function.Injective (fun γ : Fin l → Fin d => (Fin.cons j γ : Fin (l + 1) → Fin d)) :=
    fun γ γ' h => Fin.cons_right_injective (α := fun _ : Fin (l + 1) => Fin d) j (by simpa using h)
  calc ∑ γ : Fin l → Fin d, |partialDeriv (Fin.cons j γ : Fin (l + 1) → Fin d) F y|
      = ∑ γ' ∈ (Finset.univ : Finset (Fin l → Fin d)).image (fun γ => (Fin.cons j γ : Fin (l + 1) → Fin d)),
          |partialDeriv γ' F y| := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    _ ≤ ∑ γ' : Fin (l + 1) → Fin d, |partialDeriv γ' F y| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ _ := sa12z3_sum_pd_le_T hl F y

/-- Pointwise bound of the Leibniz remainder. -/
theorem sa12z3_Rj_pt {m n : ℕ} (hn : n ≤ m) {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a)
    (hF : ContDiff ℝ ∞ F) {Ka : ℝ} (hKa : ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka)
    (idx : Fin n → Fin d) (j : Fin d) (y : Euc d) :
    |sa12z3_Rj a F idx j y| ≤ Ka * 2 ^ m * sa12z3_T m F y := by
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa 0 (Nat.zero_le _) y)
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
      have hka := hKa k (by omega) y
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
