import HRS.MS.SA12X3C10B

/-!
# S.A.12 C10 (SA12X3), part C: pointwise bound of a static real-centre cutoff jet by the jets of `u`

For `a = χ(· - c)` (uniform derivative bound `B` in `c`) and `f = a u`: `(∂^idx f)^2 ≤ Kp · 1_{closedBall c 2} · Y_m(u)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_stat_B (m : ℕ) {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : Euc d) (i : ℕ), i ≤ m + 1 → ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => χ (y - c)) x‖ ≤ B := by
  have h : ∀ i : ℕ, ∃ Bi : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ Bi := fun i =>
    (hc.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top))
  choose Bi hBi using h
  refine ⟨∑ i ∈ Finset.range (m + 2), |Bi i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun c i hi x => ?_⟩
  rw [iteratedFDeriv_comp_sub]
  calc _ ≤ Bi i := hBi i _
    _ ≤ |Bi i| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun i => |Bi i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))

/-- `‖D^k u‖^2 ≤ d^k Y_m(u)`. -/
theorem sa12x3_normsq_le_Y {m k : ℕ} (hk : k ≤ m) (u : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k u x‖ ^ 2 ≤ (d : ℝ) ^ k * sa12z3_Y m u x := by
  have h1 := sa12z3_norm_iter_le u x k
  have h2 : (∑ γ : Fin k → Fin d, |partialDeriv γ u x|) ^ 2 ≤
      (Finset.univ : Finset (Fin k → Fin d)).card * ∑ γ : Fin k → Fin d, |partialDeriv γ u x| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((Finset.univ : Finset (Fin k → Fin d)).card : ℝ) = (d : ℝ) ^ k := by
    simp
  have h3 : ∑ γ : Fin k → Fin d, |partialDeriv γ u x| ^ 2 ≤ sa12z3_Y m u x := by
    simp only [sq_abs]
    unfold sa12z3_Y
    exact Finset.single_le_sum (f := fun r => ∑ γ : Fin r → Fin d, partialDeriv γ u x ^ 2)
      (fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  calc ‖iteratedFDeriv ℝ k u x‖ ^ 2 ≤ (∑ γ : Fin k → Fin d, |partialDeriv γ u x|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ (d : ℝ) ^ k * sa12z3_Y m u x := by
        rw [hcard]; exact mul_le_mul_of_nonneg_left h3 (by positivity)

open Classical in
theorem sa12x3_stat_pt (hd : 1 ≤ d) {m : ℕ} {χ : Euc d → ℝ} (hχc : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ ball (0 : Euc d) 2) {B : ℝ} (hB0 : 0 ≤ B) (c : Euc d)
    (hB : ∀ i ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ i (fun y => χ (y - c)) x‖ ≤ B)
    {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d) (x : Euc d) :
    (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2 ≤
      B ^ 2 * 4 ^ m * ((m : ℝ) + 1) ^ 2 * (d : ℝ) ^ m *
        (if x ∈ closedBall c 2 then sa12z3_Y m u x else 0) := by
  have ha : ContDiff ℝ (m + 1 : ℕ) (fun y => χ (y - c)) :=
    (sa12z3_cd_of_inf hχc _).comp (contDiff_id.sub contDiff_const)
  have hF := sa12z3_cd_of_inf hu (m + 1)
  have hY : 0 ≤ sa12z3_Y m u x := by
    unfold sa12z3_Y
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  split_ifs with hx
  · have hpd := sa12z3_pd_le_norm (fun y => χ (y - c) * u y) x idx
    have hl := sa12x2_leib_pt hB0 ha hF hB (j := n) (by omega) x
    have hsq : (partialDeriv idx (fun y => χ (y - c) * u y) x) ^ 2 ≤
        ‖iteratedFDeriv ℝ n (fun y => χ (y - c) * u y) x‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpd 2
    refine hsq.trans (hl.trans ?_)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hsum : ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ (n - i) u x‖ ^ 2 ≤
        ((m : ℝ) + 1) * ((d : ℝ) ^ m * sa12z3_Y m u x) := by
      calc ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ (n - i) u x‖ ^ 2
          ≤ ∑ _i ∈ Finset.range (n + 1), (d : ℝ) ^ m * sa12z3_Y m u x := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine (sa12x3_normsq_le_Y (m := m) (k := n - i) (by omega) u x).trans ?_
            exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 (by omega)) hY
        _ = ((n : ℝ) + 1) * ((d : ℝ) ^ m * sa12z3_Y m u x) := by simp
        _ ≤ _ := by
            have : (n : ℝ) ≤ m := by exact_mod_cast hn
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : ((2 : ℝ) ^ n) ^ 2 ≤ 4 ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]
      calc ((2 : ℝ) ^ 2) ^ n ≤ ((2 : ℝ) ^ 2) ^ m := pow_le_pow_right₀ (by norm_num) hn
        _ = 4 ^ m := by norm_num
    have hn1 : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hn
      linarith
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    calc B ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((n : ℝ) + 1) * ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ (n - i) u x‖ ^ 2
        ≤ B ^ 2 * 4 ^ m * ((m : ℝ) + 1) * (((m : ℝ) + 1) * ((d : ℝ) ^ m * sa12z3_Y m u x)) := by
          have hs0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ (n - i) u x‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => by positivity
          have e1 : B ^ 2 * ((2 : ℝ) ^ n) ^ 2 ≤ B ^ 2 * 4 ^ m := mul_le_mul_of_nonneg_left h4 (by positivity)
          have e2 : B ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((n : ℝ) + 1) ≤ B ^ 2 * 4 ^ m * ((m : ℝ) + 1) :=
            mul_le_mul e1 hn1 (by positivity) (by positivity)
          exact mul_le_mul e2 hsum hs0 (by positivity)
      _ = _ := by ring
  · have hsupp : tsupport (fun y => χ (y - c) * u y) ⊆ closedBall c 2 := by
      refine (tsupport_mul_subset_left).trans (closure_minimal ?_ isClosed_closedBall)
      intro y hy
      have h1 : y - c ∈ tsupport χ := subset_tsupport _ (by simpa [Function.mem_support] using hy)
      have h2 := hχs h1
      rw [mem_ball_zero_iff] at h2
      rw [mem_closedBall, dist_eq_norm]; exact h2.le
    have h0 : partialDeriv idx (fun y => χ (y - c) * u y) x = 0 := by
      by_contra hne
      exact hx (hsupp (sa12z3_pd_support idx (Function.mem_support.2 hne)))
    rw [h0]; simp

end HRS.MH.AdjointRd.Phase2SA12Near
