import HRS.MS.R26T8AP06a6

/-!
# S8.2 P06a (7): decay along a ray, the recursion constants, and the high-order bound
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

/-- Decay of `s^a (1+|log s|)^b` along `s = 2^-N r`. -/
theorem r26t8a_p06_decay_ray (b : ℕ) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Tendsto (fun N : ℕ => (((1:ℝ) / 2) ^ N * r) ^ a * (1 + |Real.log (((1:ℝ) / 2) ^ N * r)|) ^ b)
      atTop (𝓝 0) := by
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ a := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  set ρ := ((1:ℝ) / 2) ^ a with hρ
  have h := (r26t8a_p06_summable b hρ0 hρ1).tendsto_atTop_zero
  have h2 := h.mul_const (r ^ a * (1 + |Real.log r|) ^ b)
  rw [zero_mul] at h2
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) h2
  have e : (((1:ℝ) / 2) ^ N) ^ a = ρ ^ N := by
    rw [← Real.rpow_natCast ((1:ℝ) / 2) N, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have h1 : ((((1:ℝ) / 2) ^ N * r) ^ a) = ρ ^ N * r ^ a := by
    rw [Real.mul_rpow (by positivity) hr.le, e]
  have h3 := r26t8a_p06_pw3 b N hr hr1
  have h4 : ((N : ℝ) + 1) ^ b ≤ ((N : ℝ) + 2) ^ b :=
    pow_le_pow_left₀ (by positivity) (by linarith) b
  rw [h1]
  have hLr : 0 ≤ (1 + |Real.log r|) ^ b := by positivity
  calc ρ ^ N * r ^ a * (1 + |Real.log (((1:ℝ) / 2) ^ N * r)|) ^ b
      ≤ ρ ^ N * r ^ a * (((N : ℝ) + 2) ^ b * (1 + |Real.log r|) ^ b) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right h4 hLr)) (by positivity)
    _ = ((N : ℝ) + 2) ^ b * ρ ^ N * (r ^ a * (1 + |Real.log r|) ^ b) := by ring

/-- Constants of the downward recursion: `beta 0 = beta0`, `beta (i+1) = beta i * K(theta - (m-(i+1)))`. -/
def r26t8a_p06_beta (θ : ℝ) (b m : ℕ) (β0 : ℝ) : ℕ → ℝ
  | 0 => β0
  | i + 1 => r26t8a_p06_beta θ b m β0 i * r26t8a_p06_K (θ - ((m - (i + 1) : ℕ) : ℝ)) b

theorem r26t8a_p06_beta_nonneg (θ : ℝ) (b m : ℕ) {β0 : ℝ} (h0 : 0 ≤ β0) (i : ℕ) :
    0 ≤ r26t8a_p06_beta θ b m β0 i := by
  induction i with
  | zero => exact h0
  | succ i ih => exact mul_nonneg ih (r26t8a_p06_K_nonneg _ _)

theorem r26t8a_p06_beta_step (θ : ℝ) (b m : ℕ) (β0 : ℝ) {j : ℕ} (hj : j < m) :
    r26t8a_p06_beta θ b m β0 (m - j) =
      r26t8a_p06_beta θ b m β0 (m - (j + 1)) * r26t8a_p06_K (θ - j) b := by
  have h1 : m - j = (m - (j + 1)) + 1 := by omega
  rw [h1, r26t8a_p06_beta]
  have h2 : m - (m - (j + 1) + 1) = j := by omega
  rw [h2]

/-- High orders: no subtraction needed. -/
theorem r26t8a_p06_high (d : ℕ) (b k : ℕ) (σ : ℝ) (hσ : σ < 0) (j : ℕ) (hjk : j ≤ k)
    (hθj : min (-σ) (k : ℝ) ≤ j) (A : ℝ) (hA : 0 ≤ A) (h : Euc d → ℝ)
    (hjet : ∀ i ≤ k, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ i h z‖ ≤ A * r26t8a_jetEnvelope b (σ + i) ‖z‖)
    {z : Euc d} (hz : 0 < ‖z‖) (hz2 : ‖z‖ ≤ 1 / 2) :
    ‖iteratedFDeriv ℝ j h z‖ ≤ (2 + |r26t8a_p06_M (-(σ + k)) b|) * A *
      (‖z‖ ^ (min (-σ) (k : ℝ) - j) * (1 + |Real.log ‖z‖|) ^ b) := by
  have h1 := hjet j hjk z hz (by linarith)
  rw [r26t8a_p06_env_eq b _ hz (by linarith)] at h1
  have hL : 1 ≤ (1 + |Real.log ‖z‖|) ^ b := one_le_pow₀ (by linarith [abs_nonneg (Real.log ‖z‖)])
  have hM0 : 0 ≤ |r26t8a_p06_M (-(σ + k)) b| := abs_nonneg _
  have hz1 : ‖z‖ ≤ 1 := by linarith
  rcases le_total (-σ) (k : ℝ) with hc | hc
  · -- theta = -sigma
    rw [min_eq_left hc] at hθj ⊢
    have hq : -σ - j = -(σ + j) := by ring
    rw [hq]
    have hq0 : -(σ + (j : ℝ)) ≤ 0 := by linarith
    have h2 : 1 ≤ ‖z‖ ^ (-(σ + (j : ℝ))) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz hz1 hq0
    have h3 : 1 ≤ ‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b := by nlinarith
    have h4 : 0 ≤ ‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b := by linarith
    calc ‖iteratedFDeriv ℝ j h z‖ ≤ A * (1 + ‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b) := h1
      _ ≤ A * (2 * (‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b)) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
      _ ≤ (2 + |r26t8a_p06_M (-(σ + k)) b|) * A * (‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b) := by
          have := mul_nonneg hA h4
          nlinarith [mul_nonneg this hM0]
  · rw [min_eq_right hc] at hθj ⊢
    have hjk' : j = k := le_antisymm hjk (by exact_mod_cast hθj)
    subst hjk'
    rw [sub_self, Real.rpow_zero, one_mul]
    have hc0 : 0 ≤ -(σ + (j : ℝ)) := by linarith
    have h4 : ‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b ≤
        |r26t8a_p06_M (-(σ + j)) b| + (1 + |Real.log ‖z‖|) ^ b := by
      rcases hc0.lt_or_eq with hpos | hzero
      · have := r26t8a_p06_slog b hpos hz hz1
        linarith [le_abs_self (r26t8a_p06_M (-(σ + j)) b)]
      · have e0 : ‖z‖ ^ (-(σ + (j : ℝ))) = 1 := by rw [← hzero]; exact Real.rpow_zero _
        rw [e0, one_mul]; linarith
    calc ‖iteratedFDeriv ℝ j h z‖ ≤ A * (1 + ‖z‖ ^ (-(σ + (j : ℝ))) * (1 + |Real.log ‖z‖|) ^ b) := h1
      _ ≤ A * (1 + (|r26t8a_p06_M (-(σ + j)) b| + (1 + |Real.log ‖z‖|) ^ b)) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
      _ ≤ (2 + |r26t8a_p06_M (-(σ + j)) b|) * A * (1 + |Real.log ‖z‖|) ^ b := by
          nlinarith [mul_nonneg hA hM0, mul_nonneg (mul_nonneg hA hM0) (by linarith : (0:ℝ) ≤ (1 + |Real.log ‖z‖|) ^ b - 1),
            mul_nonneg hA (by linarith : (0:ℝ) ≤ (1 + |Real.log ‖z‖|) ^ b - 1)]

end HRS.MS.R26T8A
