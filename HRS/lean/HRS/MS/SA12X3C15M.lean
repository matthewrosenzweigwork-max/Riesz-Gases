import HRS.MS.SA12X3C15L

/-!
# S.A.12 C15 (SA12X3), part M: conversion of the cell Gronwall bound into the uloc norm
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_conv {X Y cs0 csτ : ℝ≥0∞} {c1 c2 A Sτ S0 τ : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h1 : ENNReal.ofReal c1 * X ≤ csτ ^ (1 / 2 : ℝ)) (hS : csτ ≤ ENNReal.ofReal Sτ)
    (hG : Sτ ≤ 2 * Real.exp (2 * A * τ) * S0) (h0 : ENNReal.ofReal S0 ≤ cs0)
    (h2 : cs0 ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c2 * Y) :
    X ≤ ENNReal.ofReal (c1⁻¹ * (Real.sqrt 2 * Real.exp (A * τ)) * c2) * Y := by
  set q : ℝ := Real.sqrt 2 * Real.exp (A * τ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hS0 : 0 ≤ S0 ∨ S0 < 0 := le_or_gt 0 S0
  have e1 : (2 : ℝ) * Real.exp (2 * A * τ) * S0 = q ^ 2 * S0 := by
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul]
    congr 2
    push_cast; ring_nf
  have step1 : csτ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal q * (ENNReal.ofReal S0) ^ (1 / 2 : ℝ) := by
    calc csτ ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (q ^ 2 * S0)) ^ (1 / 2 : ℝ) := by
          refine ENNReal.rpow_le_rpow (hS.trans (ENNReal.ofReal_le_ofReal ?_)) (by norm_num)
          rw [← e1]; exact hG
      _ = ENNReal.ofReal q * (ENNReal.ofReal S0) ^ (1 / 2 : ℝ) := by
          by_cases hs : 0 ≤ S0
          · rw [ENNReal.ofReal_mul (sq_nonneg q), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ENNReal.ofReal_rpow_of_nonneg (sq_nonneg q) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq hq0]
          · push Not at hs
            rw [ENNReal.ofReal_of_nonpos (by nlinarith [sq_nonneg q] : q ^ 2 * S0 ≤ 0),
              ENNReal.ofReal_of_nonpos hs.le]
            simp
  have step2 : ENNReal.ofReal c1 * X ≤ ENNReal.ofReal q * (ENNReal.ofReal c2 * Y) :=
    h1.trans (step1.trans (by gcongr; exact (ENNReal.rpow_le_rpow h0 (by norm_num)).trans h2))
  calc X = ENNReal.ofReal c1⁻¹ * (ENNReal.ofReal c1 * X) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc1.le), inv_mul_cancel₀ hc1.ne', ENNReal.ofReal_one,
          one_mul]
    _ ≤ ENNReal.ofReal c1⁻¹ * (ENNReal.ofReal q * (ENNReal.ofReal c2 * Y)) := by gcongr
    _ = ENNReal.ofReal (c1⁻¹ * q * c2) * Y := by
        rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hc1.le) hq0), ENNReal.ofReal_mul (inv_nonneg.2 hc1.le)]
        ring

end HRS.MH.AdjointRd.Phase2SA12Construction
