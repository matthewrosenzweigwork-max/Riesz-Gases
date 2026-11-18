import HRS.Sections.IIDAux8

/-!
# IID helper chain, part 9: rate arithmetic for the box cut-off `L`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Rates

variable {d : ℕ}

/-- `(2L+1)^d ≤ (6x)^d` when `x ≤ L ≤ 2x`, `1 ≤ L`. -/
lemma card_le_six {L : ℕ} {x : ℝ} (hL : 1 ≤ L) (hx : (L : ℝ) ≤ 2 * x) :
    (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (6 * x) ^ d := by
  push_cast
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact pow_le_pow_left₀ (by positivity) (by linarith) d

/-- smooth-distance rate. -/
lemma rate_smooth (hd : 2 ≤ d) {m : ℝ} (hm : (d : ℝ) / 2 < m) {Z Ct : ℝ} (hZ : 0 ≤ Z) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∃ L : ℕ, 1 ≤ L ∧
      8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N + 1) +
        2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) ≤
      C * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm0 : 0 < m := by linarith
  refine ⟨16 * Z * 6 ^ ((d : ℝ) / 2) + 8 * Z + 2 * Real.sqrt (2 * Ct), by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set e : ℝ := (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) with he
  set x : ℝ := (N : ℝ) ^ (1 / (2 * m)) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hN1 (by positivity)
  set L : ℕ := ⌈x⌉₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by rw [hLdef]; exact (Nat.ceil_pos.2 (by linarith)).ne')
  have hLx : x ≤ L := Nat.le_ceil x
  have hL2 : (L : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one (show 0 ≤ x by linarith); linarith
  refine ⟨L, hL1, ?_⟩
  have hsN : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  -- exponent identity
  have hexp : (1 / (2 * m)) * ((d : ℝ) / 2) - 1 / 2 = -((m - (d : ℝ) / 2) / (2 * m)) := by
    field_simp; ring
  have hxd : x ^ ((d : ℝ) / 2) = (N : ℝ) ^ ((1 / (2 * m)) * ((d : ℝ) / 2)) := by
    rw [hx, ← Real.rpow_mul hN0.le]
  have hA : Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ 6 ^ ((d : ℝ) / 2) * x ^ ((d : ℝ) / 2) := by
    calc Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ Real.sqrt ((6 * x) ^ d) :=
          Real.sqrt_le_sqrt (card_le_six hL1 hL2)
      _ = (6 * x) ^ ((d : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; ring
      _ = _ := Real.mul_rpow (by norm_num) (by linarith)
  have hA2 : 8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N) ≤
      16 * Z * 6 ^ ((d : ℝ) / 2) * e := by
    have h1 : 8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N) =
        16 * Z * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) / Real.sqrt N := by
      have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      rw [eq_div_iff hs.ne']
      calc _ = 8 * Z / N * 2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * (Real.sqrt N * Real.sqrt N) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hN0.le]; field_simp; ring
    rw [h1, div_le_iff₀ (Real.sqrt_pos.2 hN0)]
    have h2 : e * Real.sqrt N = (N : ℝ) ^ ((1 / (2 * m)) * ((d : ℝ) / 2)) := by
      rw [he, hsN, ← Real.rpow_add hN0]
      congr 1; linarith [hexp]
    calc 16 * Z * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ)
        ≤ 16 * Z * (6 ^ ((d : ℝ) / 2) * x ^ ((d : ℝ) / 2)) := by gcongr
      _ = 16 * Z * 6 ^ ((d : ℝ) / 2) * (e * Real.sqrt N) := by rw [h2, hxd]; ring
      _ = _ := by ring
  have he1 : 1 / (N : ℝ) ≤ e := by
    rw [he, one_div, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have : (m - (d : ℝ) / 2) / (2 * m) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hB : 8 * Z / N * 1 ≤ 8 * Z * e := by
    rw [mul_one, div_eq_mul_one_div]; gcongr
  have hT : 2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) ≤ 2 * Real.sqrt (2 * Ct) * e := by
    have hLpow : (L : ℝ) ^ ((d : ℝ) - 2 * m) ≤ x ^ ((d : ℝ) - 2 * m) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hLx (by linarith)
    have hxe : x ^ ((d : ℝ) - 2 * m) = e ^ 2 := by
      rw [hx, he, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; field_simp; ring
    calc 2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m)))
        ≤ 2 * Real.sqrt (2 * (Ct * e ^ 2)) := by
          gcongr
          rw [← hxe]; exact hLpow
      _ = 2 * Real.sqrt (2 * Ct) * e := by
          rw [show 2 * (Ct * e ^ 2) = (2 * Ct) * e ^ 2 by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
          ring
  calc 8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N + 1) +
        2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m)))
      = 8 * Z / N * (2 * Real.sqrt (((2 * L + 1) ^ d : ℕ) : ℝ) * Real.sqrt N) + 8 * Z / N * 1 +
        2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) := by ring
    _ ≤ 16 * Z * 6 ^ ((d : ℝ) / 2) * e + 8 * Z * e + 2 * Real.sqrt (2 * Ct) * e := by gcongr
    _ = _ := by ring


lemma log_le_two_sqrt {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Real.exp 1 * N) ≤ 2 * Real.sqrt N - 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have h1 : Real.log N = 2 * Real.log (Real.sqrt N) := by
    rw [← Real.log_rpow hs]
    · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; norm_num
  have h2 := Real.log_le_sub_one_of_pos hs
  linarith

/-- `W₁` rate. -/
lemma rate_W (hd : 2 ≤ d) {m : ℝ} (hm : (d : ℝ) / 2 < m) {Z Ct : ℝ} (hZ : 0 ≤ Z) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∃ L : ℕ, 1 ≤ L ∧
      Real.sqrt (8 * Z / N) * ((((2 * L + 1) ^ d : ℕ) : ℝ) * Real.log (Real.exp 1 * N) + 2) +
        2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) ≤
      C * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^ ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm0 : 0 < m := by linarith
  set b : ℝ := m + (d : ℝ) / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : 1 ≤ b := by rw [hb]; linarith
  set θ : ℝ := (m - (d : ℝ) / 2) / b with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) hb0
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hb0]; rw [hb]; linarith
  refine ⟨Real.sqrt (8 * Z) * (9 ^ d + 4) + 2 * Real.sqrt (2 * Ct), by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  set Λ : ℝ := Real.log (Real.exp 1 * N) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  have hΛ2 := log_le_two_sqrt hN
  rw [← hΛ] at hΛ2
  set ℓ : ℝ := Real.sqrt N / Λ with hℓ
  have hℓ0 : 0 < ℓ := div_pos hsN (by linarith)
  have hℓ2 : 1 / 2 ≤ ℓ := by
    rw [hℓ, le_div_iff₀ (by linarith)]; linarith
  have hjeq : (Λ / Real.sqrt N) ^ θ = ℓ ^ (-θ) := by
    rw [hℓ, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
  rw [hjeq]
  set y : ℝ := ℓ ^ (1 / b) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hℓ0 _
  have hy2 : 1 / 2 ≤ y := by
    calc (1 : ℝ) / 2 = (1 / 2) ^ (1 : ℝ) := by norm_num
      _ ≤ (1 / 2) ^ (1 / b) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by rw [div_le_one hb0]; exact hb1)
      _ ≤ y := Real.rpow_le_rpow (by norm_num) hℓ2 (by positivity)
  set L : ℕ := ⌈y⌉₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by rw [hLdef]; exact (Nat.ceil_pos.2 hy0).ne')
  have hLy : y ≤ L := Nat.le_ceil y
  have hL3 : (L : ℝ) ≤ 3 * y := by
    have := Nat.ceil_lt_add_one hy0.le; linarith
  refine ⟨L, hL1, ?_⟩
  have hp : (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (9 * y) ^ d := by
    push_cast
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hyd : y ^ d = ℓ ^ ((d : ℝ) / b) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]; congr 1; ring
  have hexpd : (d : ℝ) / b - 1 = -θ := by
    rw [hθ]; field_simp; rw [hb]; ring
  have hpl : (((2 * L + 1) ^ d : ℕ) : ℝ) / ℓ ≤ 9 ^ d * ℓ ^ (-θ) := by
    rw [div_le_iff₀ hℓ0]
    calc (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (9 * y) ^ d := hp
      _ = 9 ^ d * ℓ ^ ((d : ℝ) / b) := by rw [mul_pow, hyd]
      _ = 9 ^ d * ℓ ^ (-θ) * ℓ := by
          rw [mul_assoc, ← Real.rpow_add_one hℓ0.ne']
          congr 2; linarith [hexpd]
  have hl1 : 1 / ℓ ≤ 2 * ℓ ^ (-θ) := by
    have h1 : 1 / ℓ = ℓ ^ (-θ) * ℓ ^ (-(1 - θ)) := by
      rw [← Real.rpow_add hℓ0, one_div, ← Real.rpow_neg_one]; congr 1; ring
    have h2 : ℓ ^ (-(1 - θ)) ≤ 2 := by
      calc ℓ ^ (-(1 - θ)) ≤ (1 / 2) ^ (-(1 - θ)) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hℓ2 (by linarith)
        _ = 2 ^ (1 - θ) := by
            rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by norm_num
    rw [h1]
    have : 0 ≤ ℓ ^ (-θ) := by positivity
    nlinarith
  have hT1 : Real.sqrt (8 * Z / N) * ((((2 * L + 1) ^ d : ℕ) : ℝ) * Λ + 2) ≤
      Real.sqrt (8 * Z) * (9 ^ d + 4) * ℓ ^ (-θ) := by
    have e1 : Real.sqrt (8 * Z / N) = Real.sqrt (8 * Z) / Real.sqrt N := Real.sqrt_div (by positivity) _
    rw [e1]
    have h3 : (((2 * L + 1) ^ d : ℕ) : ℝ) * Λ + 2 ≤ ((((2 * L + 1) ^ d : ℕ) : ℝ) + 2) * Λ := by
      nlinarith [(Nat.cast_nonneg (α := ℝ) ((2 * L + 1) ^ d))]
    have h4 : Real.sqrt (8 * Z) / Real.sqrt N * (((((2 * L + 1) ^ d : ℕ) : ℝ) + 2) * Λ) =
        Real.sqrt (8 * Z) * ((((2 * L + 1) ^ d : ℕ) : ℝ) / ℓ + 2 * (1 / ℓ)) := by
      rw [hℓ]; field_simp
    calc Real.sqrt (8 * Z) / Real.sqrt N * ((((2 * L + 1) ^ d : ℕ) : ℝ) * Λ + 2)
        ≤ Real.sqrt (8 * Z) / Real.sqrt N * (((((2 * L + 1) ^ d : ℕ) : ℝ) + 2) * Λ) := by gcongr
      _ = Real.sqrt (8 * Z) * ((((2 * L + 1) ^ d : ℕ) : ℝ) / ℓ + 2 * (1 / ℓ)) := h4
      _ ≤ Real.sqrt (8 * Z) * (9 ^ d * ℓ ^ (-θ) + 2 * (2 * ℓ ^ (-θ))) := by gcongr
      _ = _ := by ring
  have hT2 : 2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m))) ≤ 2 * Real.sqrt (2 * Ct) * ℓ ^ (-θ) := by
    have hLpow : (L : ℝ) ^ ((d : ℝ) - 2 * m) ≤ y ^ ((d : ℝ) - 2 * m) :=
      Real.rpow_le_rpow_of_nonpos hy0 hLy (by linarith)
    have hye : y ^ ((d : ℝ) - 2 * m) = (ℓ ^ (-θ)) ^ 2 := by
      rw [hy, ← Real.rpow_mul hℓ0.le, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
      congr 1; rw [hθ]; push_cast; field_simp; ring
    calc 2 * Real.sqrt (2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m)))
        ≤ 2 * Real.sqrt (2 * (Ct * (ℓ ^ (-θ)) ^ 2)) := by
          gcongr
          rw [← hye]; exact hLpow
      _ = 2 * Real.sqrt (2 * Ct) * ℓ ^ (-θ) := by
          rw [show 2 * (Ct * (ℓ ^ (-θ)) ^ 2) = (2 * Ct) * (ℓ ^ (-θ)) ^ 2 by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
          ring
  calc _ ≤ Real.sqrt (8 * Z) * (9 ^ d + 4) * ℓ ^ (-θ) + 2 * Real.sqrt (2 * Ct) * ℓ ^ (-θ) := by gcongr
    _ = _ := by ring

end Rates

end HRS.IID
