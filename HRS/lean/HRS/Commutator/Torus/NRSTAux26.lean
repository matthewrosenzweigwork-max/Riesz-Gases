import HRS.Commutator.Torus.NRSTAux25

/-!
# NRS-T, part 26: the real-number shell-sum estimate
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

/-- `a_j^p (2N_j)^d ≤ A N^d 2^{-j}` with `a_j = (Cφ/κ^K) (2^{-j})^K`, `K = d+1`. -/
lemma nrstr_term (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) {Cφ : ℝ} (hCφ : 0 ≤ Cφ) {p : ℝ} (hp : 1 ≤ p)
    (M j : ℕ) :
    (Cφ / (r / (2 * d)) ^ (d + 1) * ((1 / 2 : ℝ) ^ j) ^ (d + 1)) ^ p *
        (2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2)) ^ d ≤
      ((Cφ / (r / (2 * d)) ^ (d + 1)) ^ p * 4 ^ d * (r / d) ^ d) *
        (((d : ℝ) * ((M : ℝ) + 1) / r) ^ d) * (1 / 2 : ℝ) ^ j := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  set u : ℝ := (1 / 2 : ℝ) ^ j with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2j : (2 : ℝ) ^ j * u = 1 := by
    rw [hu, ← mul_pow]; norm_num
  set B : ℝ := Cφ / (r / (2 * d)) ^ (d + 1) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set x : ℝ := (M : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  -- the box size
  have h2N : 2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) ≤ 4 * (2 : ℝ) ^ j * x := by
    push_cast
    have : (1 : ℝ) ≤ (2 : ℝ) ^ j * x := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    nlinarith
  have h2N0 : 0 ≤ 2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) := by positivity
  have hNx : ((d : ℝ) * x / r) ^ d = (d / r) ^ d * x ^ d := by rw [mul_div_right_comm, mul_pow]
  -- left side
  have hL1 : (B * u ^ (d + 1)) ^ p = B ^ p * u ^ ((d + 1 : ℝ) * p) := by
    rw [Real.mul_rpow hB0 (by positivity), ← Real.rpow_natCast u (d + 1), ← Real.rpow_mul hu0.le]
    push_cast; ring_nf
  have hL2 : u ^ ((d + 1 : ℝ) * p) ≤ u ^ ((d : ℝ) + 1) := by
    refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1 ?_
    nlinarith
  have hL3 : u ^ ((d : ℝ) + 1) = u ^ d * u := by
    rw [Real.rpow_add hu0, Real.rpow_natCast, Real.rpow_one]
  have hBp : 0 ≤ B ^ p := Real.rpow_nonneg hB0 _
  calc (B * u ^ (d + 1)) ^ p * (2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2)) ^ d
      ≤ (B * u ^ (d + 1)) ^ p * (4 * (2 : ℝ) ^ j * x) ^ d := by
        gcongr
    _ = B ^ p * u ^ ((d + 1 : ℝ) * p) * (4 ^ d * ((2 : ℝ) ^ j) ^ d * x ^ d) := by
        rw [hL1, mul_pow, mul_pow]
    _ ≤ B ^ p * (u ^ d * u) * (4 ^ d * ((2 : ℝ) ^ j) ^ d * x ^ d) := by
        gcongr
        rw [← hL3]; exact hL2
    _ = B ^ p * 4 ^ d * x ^ d * (((2 : ℝ) ^ j * u) ^ d) * u := by ring
    _ = B ^ p * 4 ^ d * x ^ d * u := by rw [h2j, one_pow, mul_one]
    _ = (B ^ p * 4 ^ d * (r / d) ^ d) * (((d : ℝ) * x / r) ^ d) * u := by
        rw [hNx]
        have : ((d : ℝ) / r) ^ d * (r / d) ^ d = 1 := by
          have h : (d : ℝ) / r * (r / d) = 1 := by field_simp
          rw [← mul_pow, h, one_pow]
        calc B ^ p * 4 ^ d * x ^ d * u = B ^ p * 4 ^ d * x ^ d * u * 1 := (mul_one _).symm
          _ = _ := by rw [← this]; ring

end HRS.Commutator.TorusNote
