import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# S8.1 XS (S81c), CR04: the final numerical estimate of the omitted-field bound (pure real arithmetic)
-/

set_option autoImplicit false
open scoped BigOperators

namespace HRS.Whole.S81b


set_option maxHeartbeats 1600000 in
theorem s81c_omitted_numeric {m : ℕ} {β βp Cv Cr Cq Cc Mg c S mt δ L : ℝ}
    (hβ0 : 0 < β) (hββp : β ≤ βp) (hCv : 0 ≤ Cv) (hCr : 0 ≤ Cr) (hCq : 1 ≤ Cq) (hCc : 0 ≤ Cc)
    (hc0 : 0 ≤ c) (hcMg : c ≤ Mg) (hmt0 : 0 ≤ mt)
    (hmt : mt ≤ Cq * (Cr / (2 * Real.sqrt ((m + 2 : ℕ) : ℝ))))
    (hS : |S - c| ≤ Real.sqrt (Cc * L) * (Cq * δ) + (Cq + 1) * (Cc / (2 * Real.sqrt ((m + 2 : ℕ) : ℝ))))
    (hn1 : ((m + 2 : ℕ) : ℝ)⁻¹ ≤ δ) (hn2 : δ ≤ 1) (hn3 : L / ((m + 2 : ℕ) : ℝ) ≤ δ) (hn4 : L * δ ≤ 5)
    (hL : 0 ≤ L) :
    β / ((m + 2 : ℕ) : ℝ) * (Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) + 2 * Real.sqrt ((m + 2 : ℕ) : ℝ)) +
      2 * (β / ((m + 2 : ℕ) : ℝ)) * ((m + 1 - 1 : ℕ) : ℝ) * mt +
      |β / ((m + 2 : ℕ) : ℝ) * (((m + 1 - 1 : ℕ) : ℝ) * S) - β * c| ≤
    βp * (Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg) *
      Real.sqrt δ := by
  set N : ℝ := ((m + 2 : ℕ) : ℝ) with hN
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < N := by linarith
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  have hm0 : ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
  have hmN : (m : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  have hm_0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set r : ℝ := Real.sqrt N with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hN0
  have hrr : r * r = N := Real.mul_self_sqrt hN0.le
  have hδ0 : 0 < δ := lt_of_lt_of_le (inv_pos.2 hN0) hn1
  set s : ℝ := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ0
  have hss : s * s = δ := Real.mul_self_sqrt hδ0.le
  -- 1 ≤ r s
  have h1rs : 1 ≤ r * s := by
    have : 1 ≤ N * δ := by
      calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
        _ ≤ N * δ := mul_le_mul_of_nonneg_left hn1 hN0.le
    have e : (r * s) * (r * s) = N * δ := by rw [← hrr, ← hss]; ring
    have hrs0 : 0 < r * s := by positivity
    by_contra h
    push Not at h
    nlinarith
  have hsl : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.2 hn2 |>.trans le_rfl
  have hδs : δ ≤ s := by nlinarith
  -- √L ≤ r s
  have hLrs : Real.sqrt L ≤ r * s := by
    rw [hr, hs, ← Real.sqrt_mul hN0.le]
    exact Real.sqrt_le_sqrt (by
      have := hn3
      rw [div_le_iff₀ hN0] at this; linarith)
  -- √L δ ≤ √5 s
  have hLδ : Real.sqrt L * δ ≤ Real.sqrt 5 * s := by
    have h5 : (Real.sqrt L * δ) ^ 2 ≤ (Real.sqrt 5 * s) ^ 2 := by
      have e1 : (Real.sqrt L * δ) ^ 2 = L * δ * δ := by
        rw [mul_pow, Real.sq_sqrt hL]; ring
      have e2 : (Real.sqrt 5 * s) ^ 2 = 5 * δ := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), sq, hss]
      rw [e1, e2]
      nlinarith
    exact abs_le_of_sq_le_sq' h5 (by positivity) |>.2
  have hCvs : 0 ≤ Real.sqrt Cv := Real.sqrt_nonneg _
  have hCcs : 0 ≤ Real.sqrt Cc := Real.sqrt_nonneg _
  have h5s : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hLs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hMg0 : 0 ≤ Mg := hc0.trans hcMg
  have hCq0 : 0 ≤ Cq := by linarith
  have hr1s : 1 / r ≤ s := by rw [div_le_iff₀ hr0]; linarith
  have haN : β / N * N = β := by field_simp
  have ha0 : 0 ≤ β / N := by positivity
  -- T2
  have T2 : β / N * (2 * r) ≤ 2 * β * s := by
    have : β / N * (2 * r) = 2 * β * (1 / r) := by rw [← hrr]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hr1s (by positivity)
  -- T1
  have T1 : β / N * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) ≤ β * Real.sqrt Cv * s := by
    have h1 : Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) ≤ Real.sqrt Cv * r * Real.sqrt L := by
      calc Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) ≤ Real.sqrt (Cv * N * L) :=
            Real.sqrt_le_sqrt (by gcongr)
        _ = Real.sqrt Cv * r * Real.sqrt L := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCv]
    have h2 : β / N * (Real.sqrt Cv * r * Real.sqrt L) = β * Real.sqrt Cv * (Real.sqrt L / r) := by
      rw [← hrr]; field_simp
    have h3 : Real.sqrt L / r ≤ s := by rw [div_le_iff₀ hr0]; linarith [hLrs, mul_comm r s]
    calc β / N * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) ≤ β / N * (Real.sqrt Cv * r * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left h1 ha0
      _ = β * Real.sqrt Cv * (Real.sqrt L / r) := h2
      _ ≤ β * Real.sqrt Cv * s := mul_le_mul_of_nonneg_left h3 (by positivity)
  -- T3
  have T3 : 2 * (β / N) * ((m + 1 - 1 : ℕ) : ℝ) * mt ≤ β * (Cq * Cr) * s := by
    rw [hm0]
    have h1 : 2 * (β / N) * (m : ℝ) * mt ≤ 2 * β * mt := by
      have : (β / N) * (m : ℝ) ≤ β := by
        calc (β / N) * (m : ℝ) ≤ (β / N) * N := mul_le_mul_of_nonneg_left hmN ha0
          _ = β := haN
      nlinarith
    have h2 : mt ≤ Cq * Cr * s / 2 := by
      refine hmt.trans ?_
      have : Cq * (Cr / (2 * r)) = Cq * Cr * (1 / r) / 2 := by field_simp
      rw [this]
      have := mul_le_mul_of_nonneg_left hr1s (show 0 ≤ Cq * Cr by positivity)
      linarith
    nlinarith
  -- T4
  have T4 : |β / N * (((m + 1 - 1 : ℕ) : ℝ) * S) - β * c| ≤
      β * (Real.sqrt Cc * Cq * (Real.sqrt 5 * s) + (Cq + 1) * Cc * s / 2) + 2 * β * Mg * s := by
    rw [hm0]
    have e : β / N * ((m : ℝ) * S) - β * c = (β / N * m) * (S - c) + (β / N * m - β) * c := by ring
    have hamb : β / N * m - β = -(2 * β / N) := by
      rw [hN]; push_cast; field_simp; ring
    have hmβ : β / N * (m : ℝ) ≤ β := by
      calc (β / N) * (m : ℝ) ≤ (β / N) * N := mul_le_mul_of_nonneg_left hmN ha0
        _ = β := haN
    have hmβ0 : 0 ≤ β / N * (m : ℝ) := by positivity
    have hEb : Real.sqrt (Cc * L) * (Cq * δ) + (Cq + 1) * (Cc / (2 * r)) ≤
        Real.sqrt Cc * Cq * (Real.sqrt 5 * s) + (Cq + 1) * Cc * s / 2 := by
      have h1 : Real.sqrt (Cc * L) * (Cq * δ) = Real.sqrt Cc * Cq * (Real.sqrt L * δ) := by
        rw [Real.sqrt_mul hCc]; ring
      have h2 : (Cq + 1) * (Cc / (2 * r)) = (Cq + 1) * Cc * (1 / r) / 2 := by field_simp
      rw [h1, h2]
      have h3 := mul_le_mul_of_nonneg_left hLδ (show 0 ≤ Real.sqrt Cc * Cq by positivity)
      have h4 := mul_le_mul_of_nonneg_left hr1s (show 0 ≤ (Cq + 1) * Cc by positivity)
      linarith
    have hcN : 2 * β / N * c ≤ 2 * β * Mg * s := by
      have : 2 * β / N * c ≤ 2 * β * Mg * δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
        have : 1 ≤ N * δ := by
          calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
            _ ≤ N * δ := mul_le_mul_of_nonneg_left hn1 hN0.le
        nlinarith [mul_nonneg hβ0.le hMg0, mul_nonneg hβ0.le hc0]
      nlinarith [mul_nonneg hβ0.le hMg0]
    rw [e, hamb]
    calc |β / N * m * (S - c) + -(2 * β / N) * c| ≤ |β / N * m * (S - c)| + |-(2 * β / N) * c| := abs_add_le _ _
      _ = β / N * m * |S - c| + 2 * β / N * c := by
          rw [abs_mul, abs_of_nonneg hmβ0, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hN0.le),
            abs_of_nonneg hc0]
      _ ≤ β * |S - c| + 2 * β / N * c := by
          have := mul_le_mul_of_nonneg_right hmβ (abs_nonneg (S - c))
          linarith
      _ ≤ β * (Real.sqrt Cc * Cq * (Real.sqrt 5 * s) + (Cq + 1) * Cc * s / 2) + 2 * β * Mg * s := by
          have := mul_le_mul_of_nonneg_left (hS.trans hEb) hβ0.le
          linarith
  have hK : 0 ≤ Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg := by
    have h1 : 0 ≤ Cq * Cr := mul_nonneg hCq0 hCr
    have h2 : 0 ≤ Real.sqrt Cc * Cq * Real.sqrt 5 := mul_nonneg (mul_nonneg hCcs hCq0) h5s
    have h3 : 0 ≤ (Cq + 1) * Cc / 2 := div_nonneg (mul_nonneg (by linarith) hCc) (by norm_num)
    linarith
  have hfin : β / N * (Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) + 2 * r) +
      2 * (β / N) * ((m + 1 - 1 : ℕ) : ℝ) * mt + |β / N * (((m + 1 - 1 : ℕ) : ℝ) * S) - β * c| ≤
      β * (Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg) * s := by
    have e : β / N * (Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) + 2 * r) =
        β / N * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * L) + β / N * (2 * r) := mul_add _ _ _
    have hsum : β * Real.sqrt Cv * s + 2 * β * s + β * (Cq * Cr) * s +
        (β * (Real.sqrt Cc * Cq * (Real.sqrt 5 * s) + (Cq + 1) * Cc * s / 2) + 2 * β * Mg * s) =
        β * (Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg) * s := by
      ring
    rw [e]
    linarith [T1, T2, T3, T4, hsum]
  calc _ ≤ β * (Real.sqrt Cv + 2 + Cq * Cr + Real.sqrt Cc * Cq * Real.sqrt 5 + (Cq + 1) * Cc / 2 + 2 * Mg) * s := hfin
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_right ?_ hs0.le
      exact mul_le_mul_of_nonneg_right hββp hK

end HRS.Whole.S81b
