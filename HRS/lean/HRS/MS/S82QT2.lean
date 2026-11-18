import HRS.MS.S82QRows2
import HRS.MS.S82QPairT

/-!
# S8.2 (S82Q): R07, the twice-pinned inner row
For `x != y` and `Y ~ R_{m+1}^{(y,x)}` (reference law with `m + 1` mobile particles and the two pins `y, x`,
`N = m + 3`), the row `S = sum_k G(x, y, Y_k)` of a canonical triple kernel satisfies
`E S^2 <= C A^2 <x>^{4M} <y>^{4M} pole(x,y)^2 N log(eN)`; both the variance part (weighted resampling
with the two-pin cutoff) and the nonzero conditional mean (`PinComparison` + sharp capped row) are kept.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

lemma s82q_ae_ne {d : ℕ} (hd : 2 ≤ d) (rho : Euc d → ℝ) (x : Euc d) :
    ∀ᵐ z ∂HRS.Whole.withDensityReal rho, z ≠ x := by
  have := s82p2_mu_singleton hd rho x
  rw [ae_iff]
  simpa using this

lemma s82q_lint_scale {α : Type*} [MeasurableSpace α] (μ : Measure α) (u v : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (huv : ∀ᵐ z ∂μ, u z ≤ c * v z) :
    ∫⁻ z, ENNReal.ofReal (u z) ∂μ ≤ ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (v z) ∂μ := by
  calc ∫⁻ z, ENNReal.ofReal (u z) ∂μ
      ≤ ∫⁻ z, ENNReal.ofReal c * ENNReal.ofReal (v z) ∂μ := by
        refine lintegral_mono_ae (huv.mono fun z hz => ?_)
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal hz
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma s82q_logN_nonneg {N : ℕ} (hN : 1 ≤ N) : 1 ≤ logN N := by
  unfold logN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : Real.exp 1 ≤ Real.exp 1 * N := by nlinarith [Real.exp_pos 1]
  have h2 : (1 : ℝ) ≤ Real.log (Real.exp 1) := by rw [Real.log_exp]
  exact h2.trans (Real.log_le_log (Real.exp_pos 1) this)

lemma s82q_logN_le {N : ℕ} (hN : 1 ≤ N) : logN N ≤ N := by
  unfold logN
  have h1 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' h1.ne', Real.log_exp]
  have := Real.log_le_sub_one_of_pos h1
  linarith

lemma s82q_inner_alg (C0 Cm CS A Pw Qw p L N m1 : ℝ) (hCS : 0 ≤ CS)
    (hA : 0 ≤ A) (hPw : 1 ≤ Pw) (hQw : 1 ≤ Qw) (hp : 1 ≤ p) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hm0 : 0 ≤ m1) (hm1 : m1 ≤ N) :
    4 * C0 ^ 2 * m1 * (A ^ 2 * (Pw ^ 2 * Qw ^ 2) * (CS * (Pw ^ 2 + Qw ^ 2) * p ^ 2 * L)) +
      (m1 * (A * Cm * Pw * Qw * (Pw + Qw) * p * (L / N))) ^ 2 ≤
    (8 * C0 ^ 2 * CS + 4 * Cm ^ 2) * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * N * L := by
  have hN : 0 < N := by linarith
  have hN0 : 0 ≤ N := hN.le
  have hP4 : 0 ≤ Pw ^ 4 * Qw ^ 4 := by positivity
  -- Pw^2 Qw^2 (Pw^2 + Qw^2) <= 2 Pw^4 Qw^4 and Pw Qw (Pw + Qw) <= 2 Pw^2 Qw^2
  have e1 : (Pw ^ 2 * Qw ^ 2) * (Pw ^ 2 + Qw ^ 2) ≤ 2 * (Pw ^ 4 * Qw ^ 4) := by
    have a1 : Pw ^ 2 * Qw ^ 2 * Pw ^ 2 ≤ Pw ^ 4 * Qw ^ 4 := by
      have : Qw ^ 2 ≤ Qw ^ 4 := by nlinarith [sq_nonneg Qw, sq_nonneg (Qw ^ 2 - 1), pow_le_pow_right₀ hQw (by norm_num : 2 ≤ 4)]
      nlinarith [pow_nonneg (by linarith : 0 ≤ Pw) 4]
    have a2 : Pw ^ 2 * Qw ^ 2 * Qw ^ 2 ≤ Pw ^ 4 * Qw ^ 4 := by
      have : Pw ^ 2 ≤ Pw ^ 4 := by nlinarith [pow_le_pow_right₀ hPw (by norm_num : 2 ≤ 4)]
      nlinarith [pow_nonneg (by linarith : 0 ≤ Qw) 4]
    nlinarith
  have e2 : Pw * Qw * (Pw + Qw) ≤ 2 * (Pw ^ 2 * Qw ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hPw) (sub_nonneg.2 hQw), mul_nonneg (by linarith : (0 : ℝ) ≤ Pw) (by linarith : (0 : ℝ) ≤ Qw)]
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have t1 : 4 * C0 ^ 2 * m1 * (A ^ 2 * (Pw ^ 2 * Qw ^ 2) * (CS * (Pw ^ 2 + Qw ^ 2) * p ^ 2 * L)) ≤
      8 * C0 ^ 2 * CS * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * N * L := by
    have : 4 * C0 ^ 2 * m1 * (A ^ 2 * (Pw ^ 2 * Qw ^ 2) * (CS * (Pw ^ 2 + Qw ^ 2) * p ^ 2 * L)) =
        (4 * C0 ^ 2 * CS * A ^ 2 * p ^ 2 * L * m1) * ((Pw ^ 2 * Qw ^ 2) * (Pw ^ 2 + Qw ^ 2)) := by ring
    rw [this]
    have hk : 0 ≤ 4 * C0 ^ 2 * CS * A ^ 2 * p ^ 2 * L * m1 := by
      have : 0 ≤ L := by linarith
      positivity
    calc (4 * C0 ^ 2 * CS * A ^ 2 * p ^ 2 * L * m1) * ((Pw ^ 2 * Qw ^ 2) * (Pw ^ 2 + Qw ^ 2))
        ≤ (4 * C0 ^ 2 * CS * A ^ 2 * p ^ 2 * L * N) * (2 * (Pw ^ 4 * Qw ^ 4)) := by
          apply mul_le_mul _ e1 (by positivity) (by
            have : 0 ≤ L := by linarith
            positivity)
          exact mul_le_mul_of_nonneg_left hm1 (by
            have : 0 ≤ L := by linarith
            positivity)
      _ = _ := by ring
  have t2 : (m1 * (A * Cm * Pw * Qw * (Pw + Qw) * p * (L / N))) ^ 2 ≤
      4 * Cm ^ 2 * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * N * L := by
    set T : ℝ := A * Cm * (Pw * Qw * (Pw + Qw)) * p with hT
    have hL0 : 0 ≤ L := by linarith
    have hLN2 : L ^ 2 ≤ N * L := by nlinarith
    calc (m1 * (A * Cm * Pw * Qw * (Pw + Qw) * p * (L / N))) ^ 2
        = m1 ^ 2 * (T ^ 2 * (L / N) ^ 2) := by rw [hT]; ring
      _ ≤ N ^ 2 * (T ^ 2 * (L / N) ^ 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hm1 2) (by positivity)
      _ = T ^ 2 * L ^ 2 := by field_simp
      _ ≤ 4 * Cm ^ 2 * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * L ^ 2 := by
          have h2 : (Pw * Qw * (Pw + Qw)) ^ 2 ≤ (2 * (Pw ^ 2 * Qw ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) e2 2
          have : T ^ 2 = A ^ 2 * Cm ^ 2 * (Pw * Qw * (Pw + Qw)) ^ 2 * p ^ 2 := by
            rw [hT]; ring
          rw [this]
          have hk : 0 ≤ A ^ 2 * Cm ^ 2 * p ^ 2 := by positivity
          calc A ^ 2 * Cm ^ 2 * (Pw * Qw * (Pw + Qw)) ^ 2 * p ^ 2 * L ^ 2
              = (A ^ 2 * Cm ^ 2 * p ^ 2 * L ^ 2) * (Pw * Qw * (Pw + Qw)) ^ 2 := by ring
            _ ≤ (A ^ 2 * Cm ^ 2 * p ^ 2 * L ^ 2) * (2 * (Pw ^ 2 * Qw ^ 2)) ^ 2 :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = _ := by ring
      _ ≤ 4 * Cm ^ 2 * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * (N * L) :=
          mul_le_mul_of_nonneg_left hLN2 (by positivity)
      _ = _ := by ring
  calc _ ≤ 8 * C0 ^ 2 * CS * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * N * L +
      4 * Cm ^ 2 * A ^ 2 * (Pw ^ 4 * Qw ^ 4) * p ^ 2 * N * L := add_le_add t1 t2
    _ = _ := by ring

end HRS.MS.S82Q
