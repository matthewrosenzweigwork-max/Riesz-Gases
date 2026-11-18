import HRS.Uniform.Q54cAux47

/-!
# Q54c, part 48: the elementary final inequalities
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

theorem final_bound (Lη : ℝ≥0∞) {C a b c Δ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hΔ : 0 ≤ Δ) (h1 : a ≤ C * Real.sqrt Δ) (h2 : b ≤ C * Δ) (h3 : c ≤ C * Δ) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c * Lη ≤
      ENNReal.ofReal C * (1 + Lη) * ENNReal.ofReal (Δ + Real.sqrt Δ) := by
  have hs := Real.sqrt_nonneg Δ
  have e1 : ENNReal.ofReal a ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt Δ) := by
    rw [← ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal h1
  have e2 : ENNReal.ofReal b ≤ ENNReal.ofReal C * ENNReal.ofReal Δ := by
    rw [← ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal h2
  have e3 : ENNReal.ofReal c ≤ ENNReal.ofReal C * ENNReal.ofReal Δ := by
    rw [← ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal h3
  rw [ENNReal.ofReal_add hΔ hs]
  calc ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c * Lη
      ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt Δ) + ENNReal.ofReal C * ENNReal.ofReal Δ +
        ENNReal.ofReal C * ENNReal.ofReal Δ * Lη := by gcongr
    _ = ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt Δ) + ENNReal.ofReal Δ * (1 + Lη)) := by ring
    _ ≤ ENNReal.ofReal C * ((1 + Lη) * (ENNReal.ofReal Δ + ENNReal.ofReal (Real.sqrt Δ))) := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        have hx : ENNReal.ofReal (Real.sqrt Δ) ≤ (1 + Lη) * ENNReal.ofReal (Real.sqrt Δ) :=
          calc ENNReal.ofReal (Real.sqrt Δ) = 1 * ENNReal.ofReal (Real.sqrt Δ) := (one_mul _).symm
            _ ≤ _ := by gcongr; exact le_self_add
        calc ENNReal.ofReal (Real.sqrt Δ) + ENNReal.ofReal Δ * (1 + Lη)
            ≤ (1 + Lη) * ENNReal.ofReal (Real.sqrt Δ) + (1 + Lη) * ENNReal.ofReal Δ :=
              add_le_add hx (le_of_eq (mul_comm _ _))
          _ = _ := by ring
    _ = _ := by ring

theorem sqrt_moment_le {X : ℝ≥0∞} {v : ℝ} (hv : 0 ≤ v) (h : X ≤ ENNReal.ofReal v) :
    X ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Real.sqrt v) := by
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hv (by norm_num), Real.sqrt_eq_rpow]

end HRS.Uniform.Q54c
