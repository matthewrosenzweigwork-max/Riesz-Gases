import HRS.MS.R26T8AP06a4

/-!
# S8.2 P06a (5): existence, symmetry and rate of the limit jets `T_j`
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_p06_env_eq (b : ℕ) (s' : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    r26t8a_jetEnvelope b s' s = 1 + s ^ (-s') * (1 + |Real.log s|) ^ b := by
  unfold r26t8a_jetEnvelope
  rw [min_eq_right hs1]

theorem r26t8a_p06_env_step (b : ℕ) (σ : ℝ) (j : ℕ) (hj : (j : ℝ) < -σ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    r26t8a_jetEnvelope b (σ + ((j + 1 : ℕ) : ℝ)) s ≤
      (2 + |r26t8a_p06_M (-(σ + j + 1)) b|) *
        (s ^ (min (-(σ + j)) 1 - 1) * (1 + |Real.log s|) ^ b) := by
  rw [r26t8a_p06_env_eq b _ hs hs1]
  have hL : 1 ≤ (1 + |Real.log s|) ^ b := one_le_pow₀ (by linarith [abs_nonneg (Real.log s)])
  have hL0 : 0 ≤ (1 + |Real.log s|) ^ b := by linarith
  have hexp : -(σ + ((j + 1 : ℕ) : ℝ)) = -(σ + j) - 1 := by push_cast; ring
  rw [hexp]
  have hM0 : 0 ≤ |r26t8a_p06_M (-(σ + j + 1)) b| := abs_nonneg _
  rcases le_or_gt (-(σ + j)) 1 with h | h
  · rw [min_eq_left h]
    have h1 : 1 ≤ s ^ (-(σ + j) - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
    have h2 : 0 ≤ s ^ (-(σ + j) - 1) := Real.rpow_nonneg hs.le _
    nlinarith [mul_le_mul h1 hL (by norm_num) h2]
  · rw [min_eq_right h.le, sub_self, Real.rpow_zero, one_mul]
    have hc : 0 < -(σ + j + 1) := by linarith
    have hcc : -(σ + j) - 1 = -(σ + j + 1) := by ring
    rw [hcc]
    have h3 := r26t8a_p06_slog b hc hs hs1
    have h4 : 0 ≤ r26t8a_p06_M (-(σ + j + 1)) b := by unfold r26t8a_p06_M; positivity
    rw [abs_of_nonneg h4]
    nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0:ℝ) ≤ 1 + r26t8a_p06_M (-(σ + j + 1)) b)]

/-- Decay of `s^a (1+|log s|)^b` along `s = 2^-(N+1)`. -/
theorem r26t8a_p06_decay (b : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (((1:ℝ) / 2) ^ (N + 1)) ^ a * (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b)
      atTop (𝓝 0) := by
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ a := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  set ρ := ((1:ℝ) / 2) ^ a with hρ
  have h := (r26t8a_p06_summable b hρ0 hρ1).tendsto_atTop_zero
  have h2 := h.const_mul ρ
  rw [mul_zero] at h2
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) h2
  have h1 : ((((1:ℝ) / 2) ^ (N + 1)) ^ a) = ρ * ρ ^ N := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast, pow_succ]; ring
  have h3 := r26t8a_p06_pw3 b (N + 1) (r := 1) one_pos le_rfl
  simp only [mul_one, Real.log_one, abs_zero, add_zero, one_pow] at h3
  have h4 : (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b ≤ ((N : ℝ) + 2) ^ b := by
    refine h3.trans ?_
    push_cast
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring]
  rw [h1]
  calc ρ * ρ ^ N * (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b ≤ ρ * ρ ^ N * ((N : ℝ) + 2) ^ b :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = ρ * (((N : ℝ) + 2) ^ b * ρ ^ N) := by ring

end HRS.MS.R26T8A
