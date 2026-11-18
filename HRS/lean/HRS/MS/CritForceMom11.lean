import HRS.MS.CritForceMom10

/-!
# S8.2 NormalForm packet R03, part 11: the integral of the log-weighted profile
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

/-- The majorant of the log-weighted squared-pole profile. -/
def s82n_g5 (d : ℕ) (L A r0 : ℝ) (r : ℝ) : ℝ :=
  4 * (L + 1) ^ 2 * r ^ (d - 1) + 16 +
    (4 * (L + 1) ^ 2 + 8 * ((Real.log A / s82n_critS d) ^ 2 +
      (Real.log r0 - Real.log A / s82n_critS d) ^ 2)) *
      (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1) +
    (128 / s82n_critS d ^ 2) * A * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 2)

lemma s82n_g5_intervalIntegrable (hd : 2 ≤ d) (L A r0 : ℝ) (hr0 : 0 < r0) (hA : 0 < A) :
    IntervalIntegrable (s82n_g5 d L A r0) volume 0 r0 := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
    (continuous_pow _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1)
      volume 0 r0 := by
    simpa using s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 0
  have i3 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 2)
      volume 0 r0 := s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 1
  unfold s82n_g5
  exact (((i1.const_mul _).add intervalIntegrable_const).add (i2.const_mul _)).add (i3.const_mul _)

lemma s82n_int_g5 (hd : 2 ≤ d) (L A r0 : ℝ) (hr0 : 0 < r0) (hA : 0 < A) :
    ∫ r in (0 : ℝ)..r0, s82n_g5 d L A r0 r =
      4 * (L + 1) ^ 2 * (r0 ^ d / d) + 16 * r0 +
        (4 * (L + 1) ^ 2 + 8 * ((Real.log A / s82n_critS d) ^ 2 +
          (Real.log r0 - Real.log A / s82n_critS d) ^ 2)) *
          ((Real.log (r0 ^ s82n_critS d + A) - Real.log A) / s82n_critS d) +
        (128 / s82n_critS d ^ 2) * A *
          ((1 / (s82n_critS d * 1)) * (1 / A - 1 / (r0 ^ s82n_critS d + A))) := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
    (continuous_pow _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1)
      volume 0 r0 := by
    simpa using s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 0
  have i3 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 2)
      volume 0 r0 := s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 1
  unfold s82n_g5
  rw [intervalIntegral.integral_add (((i1.const_mul _).add intervalIntegrable_const).add
      (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_add ((i1.const_mul _).add intervalIntegrable_const) (i2.const_mul _),
    intervalIntegral.integral_add (i1.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    s82n_ftc_log _ r0 A hs hr0 hA]
  have h3 := s82n_ftc_pow (s82n_critS d) r0 A hs hr0 hA 0
  norm_num at h3
  rw [integral_pow]
  have hd1 : d - 1 + 1 = d := by omega
  have : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    rw [Nat.cast_sub (by omega)]; ring
  rw [hd1, this]
  simp only [zero_pow (by omega : d ≠ 0), sub_zero, smul_eq_mul]
  rw [h3]
  ring

end HRS.MS.S82N
