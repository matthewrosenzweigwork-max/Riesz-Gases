import HRS.MS.WsStatAux2

/-!
# S21 packet B: rate algebra for S2.1 (i)/(ii)

Elementary facts on `deltaN`, `oN`, `localizationRate`, `generalLocalizationRate` used in the final assembly
(none uses an open row):

* `s21_deltaN_pos`, `s21_deltaN_le_one` (`0 < deltaN <= 1`, `N >= 2`);
* `s21_deltaN_le_rpow`: `deltaN <= 3 N^{s/d - 1}` for `0 <= s < d`; hence `s21_deltaN_le_oN`: `deltaN <= (3/C0) oN` for `C0 > 0`
  (so the `delta_N` in the covariance error is absorbed by `o_N`: TeX "`C(o_N + delta_N) <= C o_N`");
* `s21_oN_le`: `oN <= C0 + 1`;
* `s21_sqrt_le_rpow`: `sqrt x <= x^{3/20}` for `0 <= x <= 1` (the `W_1` rate from the `d_2` rate of the initial path / remainder);
* `s21_glr_le_loc`: if `E <= K1 oN`, then `generalLocalizationRate d E M2 N <= C localizationRate d s C0 N`
  (`w_N <= C z^{4/(d+4)}`, TeX L3438; the two cases `z <= 1` (choose `R = z^{-2/(d+4)}`) and `z > 1` (`R = 1`)).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_log_eN_le (N : ℕ) (hN : 1 ≤ N) : Real.log (Real.exp 1 * N) ≤ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have := Real.log_le_sub_one_of_pos hN0
  linarith

theorem s21_log_eN_pos (N : ℕ) (hN : 1 ≤ N) : 0 < Real.log (Real.exp 1 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  linarith

theorem s21_deltaN_pos {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (hN : 1 ≤ N) :
    0 < HRS.deltaN d s N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold HRS.deltaN
  split_ifs with h1 h2
  · exact inv_pos.2 hN0
  · exact mul_pos (inv_pos.2 hN0) (s21_log_eN_pos N hN)
  · exact Real.rpow_pos_of_pos hN0 _

theorem s21_deltaN_le_one {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (hN : 1 ≤ N) :
    HRS.deltaN d s N ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HRS.deltaN
  split_ifs with h1 h2
  · exact inv_le_one_of_one_le₀ hN1
  · have := s21_log_eN_le N hN
    rw [inv_mul_le_iff₀ hN0]
    linarith
  · have hd0 : (0 : ℝ) < d := by
      have : (0 : ℝ) ≤ s := hs0
      linarith
    have hs : 0 < s := by
      push Not at h1
      rcases h1.eq_or_lt with h | h
      · exact absurd h.symm h2
      · have : (0 : ℝ) ≤ d / 2 := by positivity
        linarith
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    have : 1 ≤ (d : ℝ) / s := by rw [le_div_iff₀ hs]; linarith
    linarith

theorem s21_deltaN_le_rpow {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (hN : 1 ≤ N) :
    HRS.deltaN d s N ≤ 3 * (N : ℝ) ^ (s / d - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hN0 _
  unfold HRS.deltaN
  split_ifs with h1 h2
  · have : (N : ℝ)⁻¹ = (N : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
    rw [this]
    have hsd0 : 0 ≤ s / d := by positivity
    have h3 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (s / d - 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  · -- `s = d/2`
    have hsd2 : s / d - 1 = -(1 / 2 : ℝ) := by
      rw [h2]; field_simp; ring
    rw [hsd2]
    have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hrp : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hN0.le]
      congr 1; ring
    rw [hrp]
    have hlog : Real.log (Real.exp 1 * N) ≤ 2 * Real.sqrt N := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
      have h4 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hsq
      have h5 : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
      linarith
    have hNN : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
    have e : (N : ℝ)⁻¹ * (2 * Real.sqrt N) = 2 * (Real.sqrt N)⁻¹ := by
      have h8 : (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ := by
        conv_lhs => rw [hNN]
        rw [mul_inv]
      rw [h8]
      field_simp
    have h6 : (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) ≤ (N : ℝ)⁻¹ * (2 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hN0.le)
    have h7 : 0 < (Real.sqrt N)⁻¹ := inv_pos.2 hsq
    linarith
  · have hs : 0 < s := by
      push Not at h1
      rcases h1.eq_or_lt with h | h
      · exact absurd h.symm h2
      · have : (0 : ℝ) ≤ d / 2 := by positivity
        linarith
    have h3 : (N : ℝ) ^ (1 - (d : ℝ) / s) ≤ (N : ℝ) ^ (s / d - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have e : (d : ℝ) / s + s / d - 2 = (s - d) ^ 2 / (s * d) := by
        field_simp; ring
      have : 0 ≤ (s - d) ^ 2 / (s * d) := by positivity
      linarith
    linarith

theorem s21_deltaN_le_oN {s C₀ : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hC₀ : 0 < C₀) (N : ℕ)
    (hN : 1 ≤ N) : HRS.deltaN d s N ≤ 3 / C₀ * HRS.oN d s C₀ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 := s21_deltaN_le_rpow hd hs0 hsd N hN
  have hpos : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hN0 _
  have h2 : 0 ≤ (if s = 0 then Real.log N / (2 * d * N) else 0) := by
    split_ifs
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (by positivity)
    · exact le_rfl
  have h3 : C₀ * (N : ℝ) ^ (s / d - 1) ≤ HRS.oN d s C₀ N := by
    unfold HRS.oN; linarith
  have h4 : 3 / C₀ * (C₀ * (N : ℝ) ^ (s / d - 1)) = 3 * (N : ℝ) ^ (s / d - 1) := by
    field_simp
  calc HRS.deltaN d s N ≤ 3 * (N : ℝ) ^ (s / d - 1) := h1
    _ = 3 / C₀ * (C₀ * (N : ℝ) ^ (s / d - 1)) := h4.symm
    _ ≤ 3 / C₀ * HRS.oN d s C₀ N := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem s21_oN_pos {s C₀ : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hC₀ : 0 < C₀) (N : ℕ) (hN : 1 ≤ N) :
    0 < HRS.oN d s C₀ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpos : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hN0 _
  have h2 : 0 ≤ (if s = 0 then Real.log N / (2 * d * N) else 0) := by
    split_ifs
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (by positivity)
    · exact le_rfl
  unfold HRS.oN
  have := mul_pos hC₀ hpos
  linarith

theorem s21_oN_le {s C₀ : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hC₀ : 0 ≤ C₀) (N : ℕ)
    (hN : 1 ≤ N) : HRS.oN d s C₀ N ≤ C₀ + 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hle : (N : ℝ) ^ (s / d - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    have : s / d ≤ 1 := by rw [div_le_one (by linarith)]; exact hsd.le
    linarith
  have h2 : (if s = 0 then Real.log N / (2 * d * N) else 0) ≤ 1 := by
    split_ifs
    · rw [div_le_one (by positivity)]
      have := Real.log_le_sub_one_of_pos hN0
      nlinarith
    · exact zero_le_one
  unfold HRS.oN
  have := mul_le_mul_of_nonneg_left hle hC₀
  linarith

theorem s21_sqrt_le_rpow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.sqrt x ≤ x ^ ((3 : ℝ) / 20) := by
  rcases hx0.eq_or_lt with h | h
  · subst h; simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 20 ≠ 0)]
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge h hx1 (by norm_num)

theorem s21_glr_le_loc {s C₀ K₁ M₂ : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hC₀ : 0 < C₀)
    (hK : 0 ≤ K₁) (hM : 0 ≤ M₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ E : ℝ, 0 ≤ E → E ≤ K₁ * HRS.oN d s C₀ N →
      generalLocalizationRate d E M₂ N ≤ C * localizationRate d s C₀ N := by
  set c : ℝ := 1 + Real.sqrt K₁ with hc
  set Zm : ℝ := 1 + Real.sqrt (C₀ + 1) with hZm
  have hc0 : 0 ≤ c := by positivity
  have hZm0 : 0 ≤ Zm := by positivity
  refine ⟨(c + 1 + M₂) * (1 + Zm), by positivity, ?_⟩
  intro N hN E hE hEK
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set a : ℝ := (N : ℝ) ^ (-(1 / (d : ℝ))) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have ha1 : a ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1'
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  set o : ℝ := HRS.oN d s C₀ N with ho
  have ho0 : 0 < o := s21_oN_pos hd hs0 hC₀ N hN1
  have hole : o ≤ C₀ + 1 := s21_oN_le hd hs0 hsd hC₀.le N hN1
  set z : ℝ := a + Real.sqrt o with hz
  have hz0 : 0 < z := by
    have := Real.sqrt_nonneg o
    linarith
  set θ : ℝ := 4 / ((d : ℝ) + 4) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hloc : localizationRate d s C₀ N = z ^ θ := rfl
  rw [hloc]
  have hEz : a + Real.sqrt E ≤ c * z := by
    have h1 : Real.sqrt E ≤ Real.sqrt K₁ * Real.sqrt o := by
      rw [← Real.sqrt_mul hK]
      exact Real.sqrt_le_sqrt hEK
    have h2 := Real.sqrt_nonneg o
    have h3 := Real.sqrt_nonneg K₁
    simp only [hc, hz]
    nlinarith [mul_nonneg h3 ha0.le]
  have hbdd : BddBelow (Set.range fun R : {R : ℝ // 1 ≤ R} =>
      R.1 ^ ((d : ℝ) / 2) * (a + Real.sqrt E) + (1 + M₂) * R.1 ^ (-(2 : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨R, rfl⟩
    have hR0 : 0 ≤ R.1 := by have := R.2; linarith
    have h1 : 0 ≤ R.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR0 _
    have h2 : 0 ≤ R.1 ^ (-(2 : ℝ)) := Real.rpow_nonneg hR0 _
    have h3 := Real.sqrt_nonneg E
    simp only
    have : 0 ≤ R.1 ^ ((d : ℝ) / 2) * (a + Real.sqrt E) := mul_nonneg h1 (by linarith)
    have : 0 ≤ (1 + M₂) * R.1 ^ (-(2 : ℝ)) := mul_nonneg (by linarith) h2
    linarith
  have key : ∀ R : {R : ℝ // 1 ≤ R}, generalLocalizationRate d E M₂ N ≤
      R.1 ^ ((d : ℝ) / 2) * (a + Real.sqrt E) + (1 + M₂) * R.1 ^ (-(2 : ℝ)) := fun R => ciInf_le hbdd R
  have hzθ0 : 0 ≤ z ^ θ := Real.rpow_nonneg hz0.le _
  by_cases hz1 : z ≤ 1
  · set e : ℝ := -2 / ((d : ℝ) + 4) with he
    have he0 : e ≤ 0 := by
      have : 0 ≤ 2 / ((d : ℝ) + 4) := by positivity
      rw [he]; rw [neg_div]; linarith
    have hR1 : 1 ≤ z ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz0 hz1 he0
    have h1 := key ⟨z ^ e, hR1⟩
    simp only at h1
    have hA : (z ^ e) ^ ((d : ℝ) / 2) * z = z ^ θ := by
      rw [← Real.rpow_mul hz0.le]
      conv_rhs => rw [show θ = e * ((d : ℝ) / 2) + 1 by
        rw [hθ, he]; field_simp; ring]
      rw [Real.rpow_add hz0, Real.rpow_one]
    have hB : (z ^ e) ^ (-(2 : ℝ)) = z ^ θ := by
      rw [← Real.rpow_mul hz0.le]
      congr 1
      rw [hθ, he]; ring
    have hR0 : 0 ≤ (z ^ e) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (Real.rpow_nonneg hz0.le _) _
    have h2 : (z ^ e) ^ ((d : ℝ) / 2) * (a + Real.sqrt E) ≤ c * z ^ θ := by
      calc (z ^ e) ^ ((d : ℝ) / 2) * (a + Real.sqrt E) ≤ (z ^ e) ^ ((d : ℝ) / 2) * (c * z) :=
            mul_le_mul_of_nonneg_left hEz hR0
        _ = c * ((z ^ e) ^ ((d : ℝ) / 2) * z) := by ring
        _ = c * z ^ θ := by rw [hA]
    have h3 : (1 + M₂) * (z ^ e) ^ (-(2 : ℝ)) = (1 + M₂) * z ^ θ := by rw [hB]
    have h4 : (c + 1 + M₂) * z ^ θ ≤ (c + 1 + M₂) * (1 + Zm) * z ^ θ := by
      have : (c + 1 + M₂) * 1 ≤ (c + 1 + M₂) * (1 + Zm) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right this hzθ0]
    nlinarith
  · push Not at hz1
    have h1 := key ⟨1, le_rfl⟩
    simp only [Real.one_rpow, one_mul, mul_one] at h1
    have hzZ : z ≤ Zm := by
      have : Real.sqrt o ≤ Real.sqrt (C₀ + 1) := Real.sqrt_le_sqrt hole
      simp only [hz, hZm]
      linarith
    have hzθ1 : 1 ≤ z ^ θ := Real.one_le_rpow hz1.le hθ0
    have h2 : a + Real.sqrt E + (1 + M₂) ≤ (c + 1 + M₂) * (1 + Zm) := by
      have : c * z ≤ c * Zm := mul_le_mul_of_nonneg_left hzZ hc0
      nlinarith [mul_nonneg hc0 hZm0, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + M₂) hZm0]
    have h3 : (c + 1 + M₂) * (1 + Zm) ≤ (c + 1 + M₂) * (1 + Zm) * z ^ θ := by
      have : 0 ≤ (c + 1 + M₂) * (1 + Zm) := by positivity
      nlinarith
    linarith

end HRS.MS.S21
