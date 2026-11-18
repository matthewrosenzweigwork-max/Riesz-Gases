import HRS.MS.R26T8AP07a

/-!
# S8.2 local Newton layer, packet T8A.P07 (part b): dyadic head sums
`sum_{u n > s} u_n^a l_n^c` for `a < 0`, `a = 0`, `a > 0` (`s <= 1`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

theorem r26t8a_p07_head_support (a : ℝ) (c : ℕ) (s : ℝ) (hs : 0 < s) {N : ℕ} (hN2 : ∀ n < N, s < ((1 : ℝ) / 2) ^ n)
    (hN1 : ((1 : ℝ) / 2) ^ N ≤ s) :
    ∑' n : ℕ, (if s < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) =
      ∑ n ∈ Finset.range N, (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (hN2 n (Finset.mem_range.1 hn))]
  · intro n hn
    have : N ≤ n := not_lt.1 (fun h => hn (Finset.mem_range.2 h))
    have : ((1 : ℝ) / 2) ^ n ≤ s := (pow_le_pow_of_le_one (by norm_num) (by norm_num) this).trans hN1
    rw [if_neg (not_lt.2 this)]

theorem r26t8a_p07_head_neg (a : ℝ) (ha : a < 0) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∑' n : ℕ, (if s < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤
        C * s ^ a * (1 + |Real.log s|) ^ c := by
  set ρ : ℝ := (2 : ℝ) ^ (-a) with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) (by linarith)
  have hρm : 0 < ρ - 1 := by linarith
  refine ⟨2 ^ c * 2 ^ (-a) / (ρ - 1), by positivity, fun s hs hs1 => ?_⟩
  obtain ⟨N, hN1, hN2⟩ := r26t8a_p07_first s hs
  obtain ⟨hlN, hN0⟩ := r26t8a_p07_N_bound hs hs1 hN1 hN2
  rw [r26t8a_p07_head_support a c s hs hN2 hN1]
  rcases hN0 with rfl | hNh
  · simp; positivity
  · have hu : ∀ n : ℕ, (((1 : ℝ) / 2) ^ n) ^ a = ρ ^ n := fun n => by
      have h12 : ((1 : ℝ) / 2) ^ a = ρ := by
        rw [hρ, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      rw [← Real.rpow_natCast ((1 : ℝ) / 2) n, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        h12, Real.rpow_natCast]
    have hl : ∀ n ∈ Finset.range N, (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c ≤ (2 * (1 + |Real.log s|)) ^ c := fun n hn => by
      refine pow_le_pow_left₀ (by positivity) ?_ c
      refine le_trans ?_ hlN
      have h := r26t8a_p07_l_le n (N - n)
      have : n + (N - n) = N := by have := Finset.mem_range.1 hn; omega
      rw [this] at h
      have hl2 : 1 + |Real.log (((1 : ℝ) / 2) ^ n)| ≤ 1 + |Real.log (((1 : ℝ) / 2) ^ N)| := by
        rw [r26t8a_p07_log_u, r26t8a_p07_log_u, abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]),
          abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)])]
        have : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hn).le
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
      exact hl2
    calc ∑ n ∈ Finset.range N, (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c
        ≤ ∑ n ∈ Finset.range N, ρ ^ n * (2 * (1 + |Real.log s|)) ^ c := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [hu]
          exact mul_le_mul_of_nonneg_left (hl n hn) (by positivity)
      _ = (∑ n ∈ Finset.range N, ρ ^ n) * (2 * (1 + |Real.log s|)) ^ c := by rw [Finset.sum_mul]
      _ ≤ (ρ ^ N / (ρ - 1)) * (2 * (1 + |Real.log s|)) ^ c := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [geom_sum_eq (by linarith)]
          have : 0 < ρ - 1 := by linarith
          rw [div_le_div_iff_of_pos_right this]
          linarith
      _ ≤ (2 ^ (-a) * s ^ a / (ρ - 1)) * (2 * (1 + |Real.log s|)) ^ c := by
          have hρN : ρ ^ N ≤ 2 ^ (-a) * s ^ a := by
            rw [← hu N]
            have h1 : (((1 : ℝ) / 2) ^ N) ^ a ≤ (s / 2) ^ a :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hNh.le ha.le
            rw [Real.div_rpow hs.le (by norm_num)] at h1
            calc (((1 : ℝ) / 2) ^ N) ^ a ≤ s ^ a / 2 ^ a := h1
              _ = 2 ^ (-a) * s ^ a := by rw [Real.rpow_neg (by norm_num)]; ring
          have : 0 < ρ - 1 := by linarith
          gcongr
      _ = 2 ^ c * 2 ^ (-a) / (ρ - 1) * s ^ a * (1 + |Real.log s|) ^ c := by rw [mul_pow]; ring

end HRS.MS.R26T8A
