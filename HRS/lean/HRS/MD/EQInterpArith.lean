import Mathlib

/-!
# EQ-INTERP packet: the real arithmetic of the choice of `R` and of the constants

* `d2_optimize`: from `S ≤ 2 R^{-(m-q)}(1+A) + R^{2(m₁-m)} ε` for all `R ≥ 1` and `S ≤ 2` conclude `S ≤ (2(1+A)+1) ε^{(m-q)/(2m₁-m-q)}`
  (`R = ε^{-1/(2m₁-m-q)}` for `ε ≤ 1`, TeX L4159-4161);
* `wass_const`: the constant of the `W_2` clause.
-/

noncomputable section

open scoped ENNReal NNReal

namespace HRS.MD.EQInterp

theorem d2_optimize {S ε A m q m₁ : ℝ} (hqm : q < m) (hmm : m < m₁) (hA : 0 ≤ A) (hε : 0 < ε)
    (hS : ∀ R : ℝ, 1 ≤ R → S ≤ 2 * (R ^ (-(m - q)) * (1 + A)) + (R ^ (m₁ - m)) ^ 2 * ε)
    (hS2 : S ≤ 2) :
    S ≤ (2 * (1 + A) + 1) * ε ^ ((m - q) / (2 * m₁ - m - q)) := by
  have hD : 0 < 2 * m₁ - m - q := by linarith
  set γ := (m - q) / (2 * m₁ - m - q) with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) hD
  by_cases h1 : ε ≤ 1
  · set R := ε ^ (-1 / (2 * m₁ - m - q)) with hR
    have hR1 : 1 ≤ R :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε h1 (div_nonpos_of_nonpos_of_nonneg (by norm_num) hD.le)
    have hR0 : 0 < R := by linarith
    have e1 : R ^ (-(m - q)) = ε ^ γ := by
      rw [hR, ← Real.rpow_mul hε.le]; congr 1; rw [hγ]; field_simp
    have e2 : (R ^ (m₁ - m)) ^ 2 * ε = ε ^ γ := by
      have h3 : (R ^ (m₁ - m)) ^ 2 = ε ^ (-1 / (2 * m₁ - m - q) * (m₁ - m) * 2) := by
        rw [hR, ← Real.rpow_mul hε.le, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        norm_num
      rw [h3]
      nth_rewrite 2 [← Real.rpow_one ε]
      rw [← Real.rpow_add hε]
      congr 1; rw [hγ]; field_simp; ring
    have := hS R hR1
    rw [e1, e2] at this
    have hpos : 0 ≤ ε ^ γ := Real.rpow_nonneg hε.le _
    nlinarith
  · push Not at h1
    have : 1 ≤ ε ^ γ := Real.one_le_rpow h1.le hγ0.le
    nlinarith

theorem wass_const {Cs C₁ α x : ℝ} (hCs : 0 < Cs) (hC₁ : 0 < C₁) (hα0 : 0 < α) (hα1 : α < 1)
    (hx : 0 < x) :
    (4 * ENNReal.ofReal Cs) ^ ((1 - α) / 2) * ENNReal.ofReal (2 * C₁ * x) ^ α =
      ENNReal.ofReal ((4 * Cs) ^ ((1 - α) / 2) * (2 * C₁) ^ α * x ^ α) := by
  have e4 : (4 : ℝ≥0∞) * ENNReal.ofReal Cs = ENNReal.ofReal (4 * Cs) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e4, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hα0.le, ← ENNReal.ofReal_mul (by positivity),
    Real.mul_rpow (by positivity) hx.le, mul_assoc]

end HRS.MD.EQInterp
