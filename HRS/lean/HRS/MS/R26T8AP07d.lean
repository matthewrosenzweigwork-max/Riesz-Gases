import HRS.MS.R26T8AP07c

/-!
# S8.2 local Newton layer, packet T8A.P07 (part d): dyadic sums in terms of `r = |w| in (0,2]` with the splitting at `4 u_n` versus `r`
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

theorem r26t8a_p07_head_summable (f : ℕ → ℝ) (s : ℝ) (hs : 0 < s) :
    Summable (fun n : ℕ => if s < ((1 : ℝ) / 2) ^ n then f n else 0) := by
  obtain ⟨N, hN1, hN2⟩ := r26t8a_p07_first s hs
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
  have : N ≤ n := not_lt.1 (fun h => hn (Finset.mem_range.2 h))
  have : ((1 : ℝ) / 2) ^ n ≤ s := (pow_le_pow_of_le_one (by norm_num) (by norm_num) this).trans hN1
  rw [if_neg (not_lt.2 this)]

theorem r26t8a_p07_log_quarter {r : ℝ} (hr : 0 < r) : 1 + |Real.log (r / 4)| ≤ 3 * (1 + |Real.log r|) := by
  have h4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have : Real.log (r / 4) = Real.log r - Real.log 4 := Real.log_div hr.ne' (by norm_num)
  rw [this]
  have := abs_sub (Real.log r) (Real.log 4)
  rw [abs_of_nonneg h40] at this
  nlinarith [abs_nonneg (Real.log r)]

theorem r26t8a_p07_SI (a : ℝ) (ha : 0 < a) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      Summable (fun n : ℕ => if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ∧
      ∑' n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C * r ^ a * (1 + |Real.log r|) ^ c := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_tail a ha c
  refine ⟨C * 3 ^ c, by positivity, fun r hr hr2 => ?_⟩
  obtain ⟨hsm, hle⟩ := hC (r / 4) (by positivity) (by linarith)
  refine ⟨hsm, hle.trans ?_⟩
  have h1 : (r / 4) ^ a ≤ r ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
  have h2 : (1 + |Real.log (r / 4)|) ^ c ≤ (3 * (1 + |Real.log r|)) ^ c :=
    pow_le_pow_left₀ (by positivity) (r26t8a_p07_log_quarter hr) c
  calc C * (r / 4) ^ a * (1 + |Real.log (r / 4)|) ^ c ≤ C * r ^ a * (3 * (1 + |Real.log r|)) ^ c :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 (by positivity) (by positivity)
    _ = C * 3 ^ c * r ^ a * (1 + |Real.log r|) ^ c := by rw [mul_pow]; ring

theorem r26t8a_p07_SII_neg (a : ℝ) (ha : a < 0) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      ∑' n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C * r ^ a * (1 + |Real.log r|) ^ c := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_head_neg a ha c
  refine ⟨C * 4 ^ (-a) * 3 ^ c, by positivity, fun r hr hr2 => ?_⟩
  refine (hC (r / 4) (by positivity) (by linarith)).trans ?_
  have h1 : (r / 4) ^ a = 4 ^ (-a) * r ^ a := by
    rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num)]; ring
  have h2 : (1 + |Real.log (r / 4)|) ^ c ≤ (3 * (1 + |Real.log r|)) ^ c :=
    pow_le_pow_left₀ (by positivity) (r26t8a_p07_log_quarter hr) c
  rw [h1]
  calc C * (4 ^ (-a) * r ^ a) * (1 + |Real.log (r / 4)|) ^ c ≤ C * (4 ^ (-a) * r ^ a) * (3 * (1 + |Real.log r|)) ^ c :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * 4 ^ (-a) * 3 ^ c * r ^ a * (1 + |Real.log r|) ^ c := by rw [mul_pow]; ring

theorem r26t8a_p07_SII_zero (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      ∑' n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ (0 : ℝ) *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C * (1 + |Real.log r|) ^ (c + 1) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_head_zero c
  refine ⟨C * 3 ^ (c + 1), by positivity, fun r hr hr2 => ?_⟩
  refine (hC (r / 4) (by positivity) (by linarith)).trans ?_
  have h2 : (1 + |Real.log (r / 4)|) ^ (c + 1) ≤ (3 * (1 + |Real.log r|)) ^ (c + 1) :=
    pow_le_pow_left₀ (by positivity) (r26t8a_p07_log_quarter hr) _
  calc C * (1 + |Real.log (r / 4)|) ^ (c + 1) ≤ C * (3 * (1 + |Real.log r|)) ^ (c + 1) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = C * 3 ^ (c + 1) * (1 + |Real.log r|) ^ (c + 1) := by rw [mul_pow]; ring

theorem r26t8a_p07_SII_pos (a : ℝ) (ha : 0 < a) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 4 →
      ∑' n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_head_pos a ha c
  exact ⟨C, hC0, fun r hr hr2 => hC (r / 4) (by positivity) (by linarith)⟩

end HRS.MS.R26T8A
