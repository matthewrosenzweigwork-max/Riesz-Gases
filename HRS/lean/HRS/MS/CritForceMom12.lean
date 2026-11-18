import HRS.MS.CritForceMom11

/-!
# S8.2 NormalForm packet R03, part 12: the `log(eN)^3` bound for the integral of the profile
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_alg_E4 (s A x : ℝ) (hs : 0 < s) (hA : 0 < A) (hx : 0 ≤ x) :
    (128 / s ^ 2) * A * ((1 / (s * 1)) * (1 / A - x)) ≤ 128 / s ^ 3 := by
  have h2 : (128 / s ^ 2) * A * ((1 / (s * 1)) * (1 / A - x)) =
      (128 / s ^ 3) * (1 - A * x) := by field_simp
  rw [h2]
  have : 0 ≤ A * x := mul_nonneg hA.le hx
  have : 0 ≤ 128 / s ^ 3 := by positivity
  nlinarith

/-- The constant multiplying `L^3`. -/
def s82n_B5 (d : ℕ) (β c0 r0 : ℝ) : ℝ :=
  16 * (r0 ^ d / d) + 16 * r0 +
    (16 + 16 * (|Real.log r0| + (|Real.log (β * c0)| + 1) / s82n_critS d) ^ 2) *
      (Real.log (1 + r0 ^ s82n_critS d / (β * c0)) + 1) / s82n_critS d +
    128 / s82n_critS d ^ 3

lemma s82n_B5_nonneg (hd : 1 ≤ d) (β c0 r0 : ℝ) (hβ : 0 < β) (hc0 : 0 < c0) (hr0 : 0 < r0) :
    0 ≤ s82n_B5 d β c0 r0 := by
  have hs := s82n_critS_pos hd
  have hr : 0 < r0 ^ s82n_critS d := Real.rpow_pos_of_pos hr0 _
  have hB : 0 ≤ Real.log (1 + r0 ^ s82n_critS d / (β * c0)) :=
    Real.log_nonneg (by have : 0 ≤ r0 ^ s82n_critS d / (β * c0) := by positivity
                        linarith)
  unfold s82n_B5; positivity

lemma s82n_int_g5_le (hd : 2 ≤ d) (β c0 r0 : ℝ) (hβ : 0 < β) (hc0 : 0 < c0) (hr0 : 0 < r0)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ r in (0 : ℝ)..r0, s82n_g5 d (s82n_logN N) (β * c0 / N) r0 r ≤
      s82n_B5 d β c0 r0 * s82n_logN N ^ 3 := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbc : 0 < β * c0 := mul_pos hβ hc0
  have hApos : 0 < β * c0 / N := by positivity
  rw [s82n_int_g5 hd _ _ r0 hr0 hApos]
  set l := Real.log N with hl
  have hl0 : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hN)
  have hL : s82n_logN N = 1 + l := s82n_logN_eq N hN
  rw [hL]
  set L := 1 + l with hLdef
  have hL1 : 1 ≤ L := by linarith
  set A := β * c0 / N with hA
  set s := s82n_critS d with hsdef
  have hlogA : Real.log A = Real.log (β * c0) - l := by
    rw [hA, Real.log_div hbc.ne' hN0.ne']
  set D0 := |Real.log (β * c0)| with hD0
  set D1 := |Real.log r0| with hD1
  set ℓ := Real.log A / s with hℓ
  have hℓb : |ℓ| ≤ ((D0 + 1) / s) * L := by
    rw [hℓ, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have : |Real.log A| ≤ D0 + l := by
      rw [hlogA]
      calc |Real.log (β * c0) - l| ≤ |Real.log (β * c0)| + |l| := abs_sub _ _
        _ = D0 + l := by rw [abs_of_nonneg hl0]
    have h2 : (D0 + 1) / s * L * s = (D0 + 1) * L := by field_simp
    rw [h2]
    have hD00 : 0 ≤ D0 := abs_nonneg _
    nlinarith
  set K2 := D1 + (D0 + 1) / s with hK2
  have hD10 : 0 ≤ D1 := abs_nonneg _
  have hD00 : 0 ≤ D0 := abs_nonneg _
  have hK20 : 0 ≤ K2 := by positivity
  have hℓK : |ℓ| ≤ K2 * L := by
    refine hℓb.trans ?_
    have : (D0 + 1) / s ≤ K2 := by rw [hK2]; linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hΛK : |Real.log r0 - ℓ| ≤ K2 * L := by
    calc |Real.log r0 - ℓ| ≤ |Real.log r0| + |ℓ| := abs_sub _ _
      _ ≤ D1 * L + ((D0 + 1) / s) * L := by
        gcongr
        · nlinarith
      _ = K2 * L := by rw [hK2]; ring
  have hℓ2 : ℓ ^ 2 ≤ (K2 * L) ^ 2 := by
    rw [← sq_abs ℓ]; exact pow_le_pow_left₀ (abs_nonneg _) hℓK 2
  have hΛ2 : (Real.log r0 - ℓ) ^ 2 ≤ (K2 * L) ^ 2 := by
    rw [← sq_abs (Real.log r0 - ℓ)]; exact pow_le_pow_left₀ (abs_nonneg _) hΛK 2
  -- the logarithmic factor
  have hlg0 : 0 ≤ Real.log (r0 ^ s + A) - Real.log A := by
    have hr : 0 < r0 ^ s := Real.rpow_pos_of_pos hr0 _
    have := Real.log_le_log hApos (show A ≤ r0 ^ s + A by linarith)
    linarith
  have hlg := s82n_log_bound s r0 (β * c0) N hN hs hr0 hbc
  set B0 := Real.log (1 + r0 ^ s / (β * c0)) with hB0
  have hB00 : 0 ≤ B0 := by
    have hr : 0 < r0 ^ s := Real.rpow_pos_of_pos hr0 _
    exact Real.log_nonneg (by have : 0 ≤ r0 ^ s / (β * c0) := by positivity
                              linarith)
  have hlg' : Real.log (r0 ^ s + A) - Real.log A ≤ (B0 + 1) * L := by
    have h1 : Real.log (r0 ^ s + A) - Real.log A ≤ l + B0 := hlg
    have h2 : (B0 + 1) * L = B0 + 1 + B0 * l + l := by rw [hLdef]; ring
    have h3 : 0 ≤ B0 * l := mul_nonneg hB00 hl0
    linarith
  -- coefficient
  have hLL : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by
    have : (L + 1) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [this]
  have hc : 4 * (L + 1) ^ 2 + 8 * (ℓ ^ 2 + (Real.log r0 - ℓ) ^ 2) ≤ (16 + 16 * K2 ^ 2) * L ^ 2 := by
    have h1 : (K2 * L) ^ 2 = K2 ^ 2 * L ^ 2 := by ring
    have h2 : (16 + 16 * K2 ^ 2) * L ^ 2 = 16 * L ^ 2 + 16 * (K2 ^ 2 * L ^ 2) := by ring
    rw [h2]
    rw [h1] at hℓ2 hΛ2
    linarith
  have hE3 : (4 * (L + 1) ^ 2 + 8 * (ℓ ^ 2 + (Real.log r0 - ℓ) ^ 2)) *
      ((Real.log (r0 ^ s + A) - Real.log A) / s) ≤ (16 + 16 * K2 ^ 2) * (B0 + 1) / s * L ^ 3 := by
    have h1 : (Real.log (r0 ^ s + A) - Real.log A) / s ≤ (B0 + 1) * L / s :=
      div_le_div_of_nonneg_right hlg' hs.le
    have h2 : 0 ≤ (Real.log (r0 ^ s + A) - Real.log A) / s := div_nonneg hlg0 hs.le
    calc _ ≤ ((16 + 16 * K2 ^ 2) * L ^ 2) * ((B0 + 1) * L / s) := by
          apply mul_le_mul hc h1 h2; positivity
      _ = _ := by ring
  have hE4 : (128 / s ^ 2) * A * ((1 / (s * 1)) * (1 / A - 1 / (r0 ^ s + A))) ≤ 128 / s ^ 3 * L ^ 3 := by
    have hr : 0 < r0 ^ s := Real.rpow_pos_of_pos hr0 _
    have h1 := s82n_alg_E4 s A (1 / (r0 ^ s + A)) hs hApos (by positivity)
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have : 0 ≤ 128 / s ^ 3 := by positivity
    exact h1.trans (le_mul_of_one_le_right this hL3)
  have hE1 : 4 * (L + 1) ^ 2 * (r0 ^ d / d) ≤ 16 * (r0 ^ d / d) * L ^ 3 := by
    have h0 : 0 ≤ r0 ^ d / d := by positivity
    have h1 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : 4 * (L + 1) ^ 2 ≤ 16 * L ^ 3 := by linarith
    calc 4 * (L + 1) ^ 2 * (r0 ^ d / d) ≤ 16 * L ^ 3 * (r0 ^ d / d) :=
          mul_le_mul_of_nonneg_right h2 h0
      _ = _ := by ring
  have hE2 : 16 * r0 ≤ 16 * r0 * L ^ 3 := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have : 0 ≤ 16 * r0 := by positivity
    exact le_mul_of_one_le_right this hL3
  unfold s82n_B5
  rw [← hsdef, ← hD0, ← hD1, ← hB0]
  have e : (16 + 16 * (D1 + (D0 + 1) / s) ^ 2) * (B0 + 1) / s = (16 + 16 * K2 ^ 2) * (B0 + 1) / s := by
    rw [hK2]
  have e2 : (16 + 16 * K2 ^ 2) * (B0 + 1) / s * L ^ 3 = (16 + 16 * K2 ^ 2) * (B0 + 1) / s * L ^ 3 := rfl
  rw [e]
  linarith [hE1, hE2, hE3, hE4]

end HRS.MS.S82N
