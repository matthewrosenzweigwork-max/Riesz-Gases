import HRS.MS.R26T8AP06a4
import HRS.MS.R26T8AP06a1

/-!
# S8.2 local Newton layer, packet T8A.P07 (part a): dyadic sums
`u n = (1/2)^n`, `l n = 1 + |log u n| = 1 + n log 2`.
`r26t8a_p07_tail`: `sum_{u n <= s} u_n^a l_n^c <= C s^a (1+|log s|)^c` (`a > 0`, `s <= 1`), and the sum is summable.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

theorem r26t8a_p07_log_u (n : ℕ) : Real.log (((1 : ℝ) / 2) ^ n) = -(n : ℝ) * Real.log 2 := by
  rw [Real.log_pow, one_div, Real.log_inv]; ring

theorem r26t8a_p07_l_le (n m : ℕ) :
    1 + |Real.log (((1 : ℝ) / 2) ^ (n + m))| ≤ (1 + (m : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) := by
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [r26t8a_p07_log_u, r26t8a_p07_log_u, abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) (n + m)]),
    abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) n])]
  push_cast
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_nonneg hn hl20, mul_nonneg hm hl20, mul_nonneg (mul_nonneg hn hm) hl20,
    mul_le_mul_of_nonneg_left hl2 (mul_nonneg hn hm)]

/-- the first dyadic index below `s`. -/
theorem r26t8a_p07_first (s : ℝ) (hs : 0 < s) : ∃ N : ℕ, ((1 : ℝ) / 2) ^ N ≤ s ∧ (∀ n < N, s < ((1 : ℝ) / 2) ^ n) := by
  have hex : ∃ n : ℕ, ((1 : ℝ) / 2) ^ n ≤ s := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hs (by norm_num : (1 : ℝ) / 2 < 1)
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun n hn => ?_⟩
  have := Nat.find_min hex hn
  push Not at this; exact this

theorem r26t8a_p07_N_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {N : ℕ} (h1 : ((1 : ℝ) / 2) ^ N ≤ s)
    (h2 : ∀ n < N, s < ((1 : ℝ) / 2) ^ n) :
    1 + |Real.log (((1 : ℝ) / 2) ^ N)| ≤ 2 * (1 + |Real.log s|) ∧ (N = 0 ∨ s / 2 < ((1 : ℝ) / 2) ^ N) := by
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨by simp; nlinarith [abs_nonneg (Real.log s)], Or.inl rfl⟩
  · refine ⟨?_, Or.inr ?_⟩
    · have h3 := h2 (N - 1) (by omega)
      have h4 : Real.log s < Real.log (((1 : ℝ) / 2) ^ (N - 1)) := Real.log_lt_log hs h3
      rw [r26t8a_p07_log_u] at h4 ⊢
      have h5 : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
      rw [abs_of_nonpos h5, abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
      have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; simp
      rw [this] at h4
      nlinarith
    · have h3 := h2 (N - 1) (by omega)
      have : ((1 : ℝ) / 2) ^ N = ((1 : ℝ) / 2) ^ (N - 1) * (1 / 2) := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; linarith

theorem r26t8a_p07_tail (a : ℝ) (ha : 0 < a) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => if ((1 : ℝ) / 2) ^ n ≤ s then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ∧
      ∑' n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ s then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C * s ^ a * (1 + |Real.log s|) ^ c := by
  set ρ : ℝ := ((1 : ℝ) / 2) ^ a with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hsum := r26t8a_p06_summable c hρ0 hρ1
  set C0 : ℝ := ∑' m : ℕ, ((m : ℝ) + 2) ^ c * ρ ^ m with hC0
  refine ⟨2 ^ c * C0, by positivity, fun s hs hs1 => ?_⟩
  obtain ⟨N, hN1, hN2⟩ := r26t8a_p07_first s hs
  obtain ⟨hlN, -⟩ := r26t8a_p07_N_bound hs hs1 hN1 hN2
  set g : ℕ → ℝ := fun n => if ((1 : ℝ) / 2) ^ n ≤ s then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0 with hg
  have hlow : ∀ n < N, g n = 0 := fun n hn => by
    simp only [hg]; rw [if_neg (not_le.2 (hN2 n hn))]
  have hup : ∀ m : ℕ, g (m + N) ≤ (2 * (1 + |Real.log s|)) ^ c * s ^ a * (((m : ℝ) + 2) ^ c * ρ ^ m) := by
    intro m
    have hle : ((1 : ℝ) / 2) ^ (m + N) ≤ s := by
      calc ((1 : ℝ) / 2) ^ (m + N) ≤ ((1 : ℝ) / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ ≤ s := hN1
    simp only [hg]; rw [if_pos hle]
    have e1 : ((1 : ℝ) / 2) ^ (m + N) = ((1 : ℝ) / 2) ^ m * ((1 : ℝ) / 2) ^ N := by rw [pow_add]
    have h1 : (((1 : ℝ) / 2) ^ (m + N)) ^ a ≤ ρ ^ m * s ^ a := by
      rw [e1, Real.mul_rpow (by positivity) (by positivity)]
      have : (((1 : ℝ) / 2) ^ m) ^ a = ρ ^ m := by
        rw [hρ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
          mul_comm]
      rw [this]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hN1 ha.le) (by positivity)
    have h2 : (1 + |Real.log (((1 : ℝ) / 2) ^ (m + N))|) ^ c ≤ (((m : ℝ) + 2) * (2 * (1 + |Real.log s|))) ^ c := by
      refine pow_le_pow_left₀ (by positivity) ?_ c
      have := r26t8a_p07_l_le N m
      rw [add_comm m N] at *
      calc 1 + |Real.log (((1 : ℝ) / 2) ^ (N + m))| ≤ (1 + (m : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ N)|) := by
            simpa [add_comm] using r26t8a_p07_l_le N m
        _ ≤ ((m : ℝ) + 2) * (2 * (1 + |Real.log s|)) := by
            refine mul_le_mul (by linarith) hlN (by positivity) (by positivity)
    calc (((1 : ℝ) / 2) ^ (m + N)) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ (m + N))|) ^ c
        ≤ (ρ ^ m * s ^ a) * (((m : ℝ) + 2) * (2 * (1 + |Real.log s|))) ^ c :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (2 * (1 + |Real.log s|)) ^ c * s ^ a * (((m : ℝ) + 2) ^ c * ρ ^ m) := by rw [mul_pow]; ring
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hsm : Summable (fun m : ℕ => g (m + N)) :=
    Summable.of_nonneg_of_le (fun m => hg0 _) hup (hsum.mul_left _)
  have hsm' : Summable g := (summable_nat_add_iff N).1 hsm
  refine ⟨hsm', ?_⟩
  rw [← hsm'.sum_add_tsum_nat_add N, Finset.sum_eq_zero (fun n hn => hlow n (Finset.mem_range.1 hn)), zero_add]
  calc ∑' m : ℕ, g (m + N) ≤ ∑' m : ℕ, (2 * (1 + |Real.log s|)) ^ c * s ^ a * (((m : ℝ) + 2) ^ c * ρ ^ m) :=
        hsm.tsum_le_tsum hup (hsum.mul_left _)
    _ = (2 * (1 + |Real.log s|)) ^ c * s ^ a * C0 := by rw [tsum_mul_left]
    _ = 2 ^ c * C0 * s ^ a * (1 + |Real.log s|) ^ c := by rw [mul_pow]; ring

end HRS.MS.R26T8A
