import HRS.MS.Fp81S21WeightedRellich3

/-!
On bounded spatial regions, the target Japanese-bracket weight is bounded
above.  This lemma is a useful bridge from the unweighted `L²` convergence
of a localized derivative coordinate to its weighted `L²` convergence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- The target weighted `L²` energy of a scalar coordinate. -/
def fp81s21_weightedRellich_L2Energy (P : ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (u x) ^ 2)

/-- The Japanese-bracket weight is globally at most `2^P` for nonnegative
`P`; consequently weighted `L²` energy is controlled by unweighted energy. -/
theorem fp81s21_weightedRellich_weightedL2_le
    {P : ℝ} (hP : 0 ≤ P) (u : Euc d → ℝ) :
    fp81s21_weightedRellich_L2Energy (d := d) P u ≤
      ENNReal.ofReal (2 ^ P) *
        (∫⁻ x, ENNReal.ofReal ((u x) ^ 2)) := by
  have hcoef : 0 ≤ (2 : ℝ) ^ P := Real.rpow_nonneg (by norm_num) _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ P) * ENNReal.ofReal ((u x) ^ 2) := by
      unfold fp81s21_weightedRellich_L2Energy
      apply lintegral_mono
      intro x
      have hw := s57pW_le (d := d) hP x
      change jbracket x ^ (-2 * P) ≤
        2 ^ P * (1 + ‖x‖) ^ (-(2 * P)) at hw
      have hw : jbracket x ^ (-2 * P) ≤
          2 ^ P * (1 + ‖x‖) ^ (-2 * P) := by
        have hExp : -(2 * P) = -2 * P := by ring
        rw [hExp] at hw
        exact hw
      have hbase : (1 : ℝ) ≤ 1 + ‖x‖ := by nlinarith [norm_nonneg x]
      have hpow : (1 + ‖x‖) ^ (-2 * P) ≤ 1 := by
        calc
          _ ≤ (1 : ℝ) ^ (-2 * P) := Real.rpow_le_rpow_of_nonpos
            one_pos hbase (by linarith)
          _ = 1 := Real.one_rpow _
      have hw' : jbracket x ^ (-2 * P) ≤ 2 ^ P := by
        calc
          _ ≤ 2 ^ P * (1 + ‖x‖) ^ (-2 * P) := hw
          _ ≤ 2 ^ P := by nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]
      have hsq : 0 ≤ (u x) ^ 2 := sq_nonneg _
      calc
        ENNReal.ofReal (jbracket x ^ (-2 * P) * (u x) ^ 2)
            ≤ ENNReal.ofReal (2 ^ P * (u x) ^ 2) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw' hsq)
        _ = ENNReal.ofReal (2 ^ P) * ENNReal.ofReal ((u x) ^ 2) :=
              ENNReal.ofReal_mul hcoef
    _ = ENNReal.ofReal (2 ^ P) *
        (∫⁻ x, ENNReal.ofReal ((u x) ^ 2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_weightedL2_le

end HRS.Fp81.S21
