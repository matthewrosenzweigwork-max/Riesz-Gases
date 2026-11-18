import HRS.MS.R2WinErrAux7

/-!
# S10.4 packet E2c: `generalLocalizationRate` with `E_N = C o_N` against the explicit `localizationRate`

`s104_glr_le`: for `N ≥ 2`, `inf_{R ≥ 1}{R^{d/2}(N^{-1/d} + √(C_e o_N)) + (1+M₂)R^{-2}} ≤ C_g (N^{-1/d} + √o_N)^{4/(d+4)}`
with `C_g` independent of `N` (`w_N ≤ C z_N^{4/(d+4)}`, S L3446, including the range `z_N > 1`, where `z_N` is bounded
uniformly in `N ≥ 2`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.R2WinErr

open HRS.Whole

lemma s104_oN_le (d : ℕ) (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (N : ℕ) (hN : 2 ≤ N) : HRS.oN d s C₀ N ≤ C₀ + 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  unfold HRS.oN
  have h1 : (N : ℝ) ^ (s / d - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    have : s / d < 1 := by rw [div_lt_one hdpos]; exact hsd
    linarith
  have h2 : (if s = 0 then Real.log N / (2 * d * N) else 0) ≤ 1 := by
    split_ifs
    · rw [div_le_one (by positivity)]
      have := Real.log_le_sub_one_of_pos hNpos
      have hd2 : (1 : ℝ) ≤ 2 * d := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        linarith
      nlinarith
    · norm_num
  have h3 : C₀ * (N : ℝ) ^ (s / d - 1) ≤ C₀ := by
    calc C₀ * (N : ℝ) ^ (s / d - 1) ≤ C₀ * 1 := mul_le_mul_of_nonneg_left h1 hC₀
      _ = C₀ := mul_one _
  linarith

theorem s104_glr_le (d : ℕ) (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (C₀ Cen M₂ : ℝ)
    (hC₀ : 0 ≤ C₀) (hCen : 0 ≤ Cen) (hM₂ : 0 ≤ M₂) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N : ℕ, 2 ≤ N →
      generalLocalizationRate d (Cen * HRS.oN d s C₀ N) M₂ N ≤ Cg * localizationRate d s C₀ N := by
  set κ : ℝ := max 1 (Real.sqrt Cen) with hκ
  have hκ1 : 1 ≤ κ := le_max_left _ _
  have hκs : Real.sqrt Cen ≤ κ := le_max_right _ _
  set Y : ℝ := κ * (1 + Real.sqrt (C₀ + 1)) with hY
  refine ⟨κ + 1 + M₂ + Y + 1, by positivity, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  set n : ℝ := (N : ℝ) ^ (-(1 / (d : ℝ))) with hn
  have hnpos : 0 < n := Real.rpow_pos_of_pos hNpos _
  have hn1 : n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith)
  set o : ℝ := HRS.oN d s C₀ N with ho
  set e : ℝ := Real.sqrt o with he
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hoY : o ≤ C₀ + 1 := s104_oN_le d hd1 s hs0 hsd C₀ hC₀ N hN
  have heY : e ≤ Real.sqrt (C₀ + 1) := Real.sqrt_le_sqrt hoY
  set y : ℝ := n + e with hy
  have hypos : 0 < y := by positivity
  have hyY : y ≤ 1 + Real.sqrt (C₀ + 1) := by linarith
  have hloc : localizationRate d s C₀ N = y ^ (4 / ((d : ℝ) + 4)) := rfl
  rw [hloc]
  have hq0 : 0 ≤ 4 / ((d : ℝ) + 4) := by positivity
  -- the bound of the integrand at the energy level `Cen * o`
  have hz : n + Real.sqrt (Cen * o) ≤ κ * y := by
    rw [Real.sqrt_mul hCen]
    have : Real.sqrt Cen * e ≤ κ * e := mul_le_mul_of_nonneg_right hκs he0
    nlinarith
  have hbdd : BddBelow (Set.range (fun R : {R : ℝ // 1 ≤ R} =>
      R.1 ^ ((d : ℝ) / 2) * (n + Real.sqrt (Cen * o)) + (1 + M₂) * R.1 ^ (-(2 : ℝ)))) :=
    ⟨0, by
      rintro _ ⟨R, rfl⟩
      have : 0 < R.1 := by linarith [R.2]
      positivity⟩
  have key : ∀ R : ℝ, 1 ≤ R → generalLocalizationRate d (Cen * o) M₂ N ≤
      R ^ ((d : ℝ) / 2) * (n + Real.sqrt (Cen * o)) + (1 + M₂) * R ^ (-(2 : ℝ)) :=
    fun R hR => ciInf_le hbdd ⟨R, hR⟩
  have hyq : 0 ≤ y ^ (4 / ((d : ℝ) + 4)) := Real.rpow_nonneg hypos.le _
  have hCg : κ + 1 + M₂ ≤ κ + 1 + M₂ + Y + 1 := by
    have : 0 ≤ Y := by positivity
    linarith
  by_cases hy1 : y ≤ 1
  · set R : ℝ := y ^ (-(2 / ((d : ℝ) + 4))) with hR
    have hR1 : 1 ≤ R := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hypos hy1 (by
      have : 0 ≤ 2 / ((d : ℝ) + 4) := by positivity
      linarith)
    have hRpos : 0 < R := by linarith
    have e1 : R ^ ((d : ℝ) / 2) = y ^ (-((d : ℝ) / ((d : ℝ) + 4))) := by
      rw [hR, ← Real.rpow_mul hypos.le]
      congr 1; field_simp
    have e2 : R ^ (-(2 : ℝ)) = y ^ (4 / ((d : ℝ) + 4)) := by
      rw [hR, ← Real.rpow_mul hypos.le]
      congr 1; field_simp; ring
    have e3 : y ^ (-((d : ℝ) / ((d : ℝ) + 4))) * y = y ^ (4 / ((d : ℝ) + 4)) := by
      have : 4 / ((d : ℝ) + 4) = -((d : ℝ) / ((d : ℝ) + 4)) + 1 := by field_simp; ring
      rw [this, Real.rpow_add hypos, Real.rpow_one]
    refine (key R hR1).trans ?_
    have hRd : 0 ≤ R ^ ((d : ℝ) / 2) := Real.rpow_nonneg hRpos.le _
    calc R ^ ((d : ℝ) / 2) * (n + Real.sqrt (Cen * o)) + (1 + M₂) * R ^ (-(2 : ℝ))
        ≤ R ^ ((d : ℝ) / 2) * (κ * y) + (1 + M₂) * R ^ (-(2 : ℝ)) := by gcongr
      _ = (κ + (1 + M₂)) * y ^ (4 / ((d : ℝ) + 4)) := by
          rw [e1, e2, mul_left_comm, ← e3]; ring
      _ ≤ (κ + 1 + M₂ + Y + 1) * y ^ (4 / ((d : ℝ) + 4)) := by
          have hY0 : 0 ≤ Y := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) hyq
  · push Not at hy1
    refine (key 1 le_rfl).trans ?_
    rw [Real.one_rpow, one_mul, Real.one_rpow, mul_one]
    have hyq1 : 1 ≤ y ^ (4 / ((d : ℝ) + 4)) := Real.one_le_rpow hy1.le hq0
    have h1 : n + Real.sqrt (Cen * o) + (1 + M₂) ≤ Y + 1 + M₂ := by
      have : κ * y ≤ Y := mul_le_mul_of_nonneg_left hyY (by linarith)
      linarith
    calc n + Real.sqrt (Cen * o) + (1 + M₂) ≤ κ + 1 + M₂ + Y + 1 := by linarith
      _ ≤ (κ + 1 + M₂ + Y + 1) * y ^ (4 / ((d : ℝ) + 4)) :=
          le_mul_of_one_le_right (by positivity) hyq1

end HRS.MS.R2WinErr
