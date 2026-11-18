import HRS.MH.CoercLowerDefs
import Mathlib

/-!
# CoercLower packet P30 (`param_log`): choice of `T = (NΛ)^{2/d}` in the case `s = 0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- [P30] Choice of `T = (NΛ)^{2/d}`; the constant depends on `d` only (`1/4 + d!/2 + π^{d/2}/d`). -/
theorem param_log (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      1 ≤ ((N : ℝ) * Λ) ^ (2 / (d : ℝ)) ∧
      (1 / 2) *
          ((1 + Real.log (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) / (2 * N) +
            Real.exp (-(((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) +
            2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / d *
              (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) ^ (-((d : ℝ) / 2)))) ≤
        Real.log ((N : ℝ) * Λ) / (2 * d * N) + C / N := by
  refine ⟨1 / 4 + (d.factorial : ℝ) / 2 + Real.pi ^ ((d : ℝ) / 2) / d, ?_, ?_⟩
  · positivity
  intro Λ hΛ N hN
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  set M : ℝ := (N : ℝ) * Λ with hM
  have hM1 : 1 ≤ M := by nlinarith [hM, hNpos, hΛ]
  have hM0 : 0 < M := by linarith
  have hMN : (N : ℝ) ≤ M := by nlinarith [hM, hNpos, hΛ]
  set T : ℝ := M ^ (2 / (d : ℝ)) with hT
  have hT1 : 1 ≤ T := by
    rw [hT]; exact Real.one_le_rpow hM1 (by positivity)
  have hT0 : 0 < T := by linarith
  have hTd : T ^ d = M ^ 2 := by
    have h2d : (2 / (d : ℝ)) * (d : ℝ) = 2 := by field_simp
    rw [hT, ← Real.rpow_natCast (M ^ (2 / (d : ℝ))) d, ← Real.rpow_mul hM0.le, h2d, Real.rpow_two]
  have hlogT : Real.log T = 2 / (d : ℝ) * Real.log M := by
    rw [hT, Real.log_rpow hM0]
  have hTneg : T ^ (-((d : ℝ) / 2)) = M⁻¹ := by
    have hh : (2 / (d : ℝ)) * (-((d : ℝ) / 2)) = -1 := by
      field_simp
    rw [hT, ← Real.rpow_mul hM0.le, hh, Real.rpow_neg_one]
  -- e^{-T} ≤ d!/T^d = d!/M^2 ≤ d!/N
  have hexpT : Real.exp (-T) ≤ (d.factorial : ℝ) / T ^ d := by
    have h1 := Real.pow_div_factorial_le_exp T hT0.le d
    have hpos : 0 < T ^ d / (d.factorial : ℝ) := by positivity
    rw [Real.exp_neg, ← inv_div]
    exact inv_anti₀ hpos h1
  have hNT : (N : ℝ) ≤ T ^ d := by
    rw [hTd]; nlinarith [hMN, hM1]
  have hexp_bd : Real.exp (-T) ≤ (d.factorial : ℝ) / N := by
    refine le_trans hexpT ?_
    gcongr
  have hB2 : (1 / 2) * Real.exp (-T) ≤ (d.factorial : ℝ) / (2 * N) := by
    have : (d.factorial : ℝ) / (2 * N) = (1 / 2) * ((d.factorial : ℝ) / N) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hexp_bd (by norm_num)
  -- the logarithmic and the Λ-terms
  have key : (1 / 2) *
      ((1 + Real.log T) / (2 * N) + Real.exp (-T) +
        2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2)))) =
      1 / (4 * N) + Real.log M / (2 * d * N) + (1 / 2) * Real.exp (-T) +
        Real.pi ^ ((d : ℝ) / 2) / (d * N) := by
    rw [hTneg, hlogT, hM]
    field_simp
    ring
  have hrhs : Real.log M / (2 * d * N) + (1 / 4 + (d.factorial : ℝ) / 2 + Real.pi ^ ((d : ℝ) / 2) / d) / N =
      Real.log M / (2 * d * N) + 1 / (4 * N) + (d.factorial : ℝ) / (2 * N) +
        Real.pi ^ ((d : ℝ) / 2) / (d * N) := by
    field_simp
    ring
  refine ⟨hT1, ?_⟩
  rw [key]
  have hB2' := hB2
  rw [hrhs]
  linarith

end HRS.MH.CoercLower
