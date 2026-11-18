import HRS.MS.CritForceMom9

/-!
# S8.2 NormalForm packet R03, part 10: profile bound for the log-weighted squared-pole row
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_E5_profile (hd : 2 ≤ d) (L A r0 r : ℝ) (hA : 0 < A) (hr : 0 < r) (hrr : r ≤ r0)
    (hr1 : r0 ≤ 1) :
    r ^ (d - 1) * ((1 + r ^ (-s82n_critS d)) ^ 2 * (L + 1 + |Real.log r|) ^ 2 *
        Real.exp (-(A * r ^ (-s82n_critS d)))) ≤
      4 * (L + 1) ^ 2 * r ^ (d - 1) + 16 +
        (4 * (L + 1) ^ 2 + 8 * ((Real.log A / s82n_critS d) ^ 2 +
          (Real.log r0 - Real.log A / s82n_critS d) ^ 2)) *
          (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1) +
        (128 / s82n_critS d ^ 2) * A * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 2) := by
  have hr1' : r ≤ 1 := hrr.trans hr1
  obtain ⟨f1, f2, f3, -⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have hlog2 := s82n_log_sq_le (s82n_critS d) r0 A r hs hA hr hrr
  have hlog1 := s82n_log_sq_le_inv r hr hr1'
  have hPr : r ^ (d - 1) ≤ r := by
    have := pow_le_pow_of_le_one hr.le hr1' (show 1 ≤ d - 1 by omega)
    simpa using this
  have hP0 : 0 ≤ r ^ (d - 1) := by positivity
  set P := r ^ (d - 1) with hP
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  set q := r ^ (s82n_critS d - 1) with hq
  set ℓ := Real.log A / s82n_critS d with hℓ
  set Λ := Real.log r0 - ℓ with hΛ
  set Z := (Real.log r) ^ 2 with hZ
  set X := (L + 1) ^ 2 with hX
  have hX0 : 0 ≤ X := sq_nonneg _
  have hZ0 : 0 ≤ Z := sq_nonneg _
  rw [f3]
  set u := w⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 hw0
  set t := A * u with ht
  have ht0 : 0 ≤ t := by positivity
  set e := Real.exp (-t) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by rw [he, Real.exp_le_one_iff]; linarith
  have he2 : e ≤ 1 / (1 + t) := s82n_exp_neg_le_one_add t ht0
  have he3 : e ≤ ((2 : ℕ) : ℝ) ^ 2 / (1 + t) ^ 2 := s82n_exp_neg_le 2 (by norm_num) t ht0
  have hF1 : (1 + u) ^ 2 ≤ 2 + 2 * u ^ 2 := by nlinarith [sq_nonneg (1 - u)]
  have hF2 : (L + 1 + |Real.log r|) ^ 2 ≤ 2 * X + 2 * Z := by
    rw [hX, hZ, ← sq_abs (Real.log r)]; nlinarith [sq_nonneg (L + 1 - |Real.log r|)]
  have hPu : P * u ^ 2 = 1 / r := by rw [f1, hu]; field_simp
  have hq' : q = w / r := f2
  have hAw : A / w = t := by rw [ht, hu]; ring
  have hlog2' : Z ≤ 2 * ℓ ^ 2 + 2 * Λ ^ 2 + (8 / s82n_critS d ^ 2) * t := by
    rw [← hAw]; exact hlog2
  -- Step A
  have hA1 : P * ((1 + u) ^ 2 * (L + 1 + |Real.log r|) ^ 2 * e) ≤
      P * ((2 + 2 * u ^ 2) * (2 * X + 2 * Z) * e) := by
    gcongr
  have hB : P * ((2 + 2 * u ^ 2) * (2 * X + 2 * Z) * e) =
      4 * X * P * e + 4 * P * Z * e + 4 * X * (1 / r) * e + 4 * (1 / r) * Z * e := by
    have : P * ((2 + 2 * u ^ 2) * (2 * X + 2 * Z) * e) =
        4 * X * P * e + 4 * P * Z * e + 4 * X * (P * u ^ 2) * e + 4 * (P * u ^ 2) * Z * e := by
      ring
    rw [this, hPu]
  have hr1inv : 0 ≤ 1 / r := by positivity
  -- Step C
  have T1 : 4 * X * P * e ≤ 4 * X * P := by
    have h0 : 0 ≤ 4 * X * P := by positivity
    calc 4 * X * P * e ≤ 4 * X * P * 1 := mul_le_mul_of_nonneg_left he1 h0
      _ = 4 * X * P := mul_one _
  have T2 : 4 * P * Z * e ≤ 16 := by
    have h1 : P * Z ≤ 4 := by
      calc P * Z ≤ P * (4 / r) := by gcongr
        _ ≤ r * (4 / r) := by gcongr
        _ = 4 := by field_simp
    have h2 : 0 ≤ P * Z := by positivity
    have h3 : 4 * P * Z * e = 4 * (P * Z) * e := by ring
    rw [h3]
    calc 4 * (P * Z) * e ≤ 4 * 4 * 1 := by gcongr
      _ = 16 := by norm_num
  have hqe1 : (1 / r) * (1 / (1 + t)) = q / (w + A) ^ 1 := by
    rw [hq', ht, hu]; field_simp
  have T3 : 4 * X * (1 / r) * e ≤ 4 * X * (q / (w + A) ^ 1) := by
    rw [← hqe1]
    have : 0 ≤ 4 * X * (1 / r) := by positivity
    calc 4 * X * (1 / r) * e ≤ 4 * X * (1 / r) * (1 / (1 + t)) := by gcongr
      _ = _ := by ring
  have T4a : 4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2) * e ≤
      8 * (ℓ ^ 2 + Λ ^ 2) * (q / (w + A) ^ 1) := by
    rw [← hqe1]
    have : 0 ≤ 4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2) := by positivity
    calc 4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2) * e ≤
        4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2) * (1 / (1 + t)) := by gcongr
      _ = _ := by ring
  have hqe2 : (1 / r) * (t * (4 / (1 + t) ^ 2)) = 4 * A * (q / (w + A) ^ 2) := by
    rw [hq', ht, hu]; field_simp
  have T4b : 4 * (1 / r) * ((8 / s82n_critS d ^ 2) * t) * e ≤
      (128 / s82n_critS d ^ 2) * A * (q / (w + A) ^ 2) := by
    have h3 : t * e ≤ t * (4 / (1 + t) ^ 2) := by
      have : ((2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num
      rw [this] at he3
      exact mul_le_mul_of_nonneg_left he3 ht0
    have h4 : 4 * (1 / r) * ((8 / s82n_critS d ^ 2) * t) * e =
        (32 / s82n_critS d ^ 2) * ((1 / r) * (t * e)) := by ring
    rw [h4]
    calc (32 / s82n_critS d ^ 2) * ((1 / r) * (t * e)) ≤
        (32 / s82n_critS d ^ 2) * ((1 / r) * (t * (4 / (1 + t) ^ 2))) := by gcongr
      _ = _ := by rw [hqe2]; ring
  have T4 : 4 * (1 / r) * Z * e ≤ 8 * (ℓ ^ 2 + Λ ^ 2) * (q / (w + A) ^ 1) +
      (128 / s82n_critS d ^ 2) * A * (q / (w + A) ^ 2) := by
    have : 4 * (1 / r) * Z * e ≤
        4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2 + (8 / s82n_critS d ^ 2) * t) * e := by gcongr
    have h5 : 4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2 + (8 / s82n_critS d ^ 2) * t) * e =
        4 * (1 / r) * (2 * ℓ ^ 2 + 2 * Λ ^ 2) * e +
          4 * (1 / r) * ((8 / s82n_critS d ^ 2) * t) * e := by ring
    linarith
  calc P * ((1 + u) ^ 2 * (L + 1 + |Real.log r|) ^ 2 * e) ≤ _ := hA1
    _ = _ := hB
    _ ≤ _ := by linarith [T1, T2, T3, T4]

end HRS.MS.S82N
