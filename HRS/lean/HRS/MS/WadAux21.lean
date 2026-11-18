import HRS.MS.WadAux20

/-!
# S8.3, packet D4 (part 2): polynomial-times-Gaussian bounds

`s84_poly_gauss`: for `p ≥ 0`, `c > 0` there is `K` with `(1+‖y‖)^p e^{-c‖y‖²} ≤ K` (all `y`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- `(1+s)^q ≤ K e^{c s}` for `s ≥ 0`. -/
theorem s84_pow_le_exp {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ q ≤ K * Real.exp (c * s) := by
  set n : ℕ := ⌈q⌉₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  have hqn : q ≤ n := by
    have := Nat.le_ceil q
    rw [hn]; push_cast; linarith
  refine ⟨(n / c) ^ q * Real.exp c, by positivity, fun s hs => ?_⟩
  set z : ℝ := c * (1 + s) / n with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  have h1 : z ^ (q / n) ≤ Real.exp z := s84_rpow_le_exp hz0 (by positivity) (by rw [div_le_one hn0]; exact hqn)
  have h2 : z ^ q ≤ Real.exp (n * z) := by
    have : z ^ q = (z ^ (q / n)) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; congr 1; field_simp
    rw [this, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hz0.le _) h1 n
  have h3 : Real.exp (n * z) = Real.exp c * Real.exp (c * s) := by
    rw [← Real.exp_add, hz]; congr 1; field_simp
  have h4 : (1 + s) ^ q = (n / c) ^ q * z ^ q := by
    rw [← Real.mul_rpow (by positivity) hz0.le, hz]; congr 1; field_simp
  rw [h4]
  calc (n / c) ^ q * z ^ q ≤ (n / c) ^ q * (Real.exp c * Real.exp (c * s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← h3]; exact h2
    _ = _ := by ring

theorem s84_poly_gauss {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Euc d, (1 + ‖y‖) ^ p * Real.exp (-c * ‖y‖ ^ 2) ≤ K := by
  obtain ⟨K, hK0, hK⟩ := s84_pow_le_exp (q := p / 2) (c := c) (by positivity) hc
  refine ⟨2 ^ (p / 2) * K, by positivity, fun y => ?_⟩
  have h1 : (1 + ‖y‖) ^ p ≤ (2 * (1 + ‖y‖ ^ 2)) ^ (p / 2) := by
    have : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖y‖)]
    calc (1 + ‖y‖) ^ p = ((1 + ‖y‖) ^ (2 : ℝ)) ^ (p / 2) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; ring
      _ ≤ (2 * (1 + ‖y‖ ^ 2)) ^ (p / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [Real.rpow_two]; exact this
  have h2 := hK (‖y‖ ^ 2) (sq_nonneg _)
  calc (1 + ‖y‖) ^ p * Real.exp (-c * ‖y‖ ^ 2)
      ≤ (2 * (1 + ‖y‖ ^ 2)) ^ (p / 2) * Real.exp (-c * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 ^ (p / 2) * ((1 + ‖y‖ ^ 2) ^ (p / 2) * Real.exp (-c * ‖y‖ ^ 2)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    _ ≤ 2 ^ (p / 2) * (K * Real.exp (c * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 ^ (p / 2) * K := by
        rw [mul_assoc, ← Real.exp_add]; simp

end HRS.MS.Wad
