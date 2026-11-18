import HRS.MS.Fp81S21WeightedRellich5

/-!
For the unit ball of the source weighted norm, the exterior contribution to
the squared target jet norm has the explicit `ρ⁻⁴` bound.  Thus the norm
contribution decays as `ρ⁻²`.  The tail is measured on `jbracket x ≥ ρ`,
which is the exterior convention used by the pointwise weight comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- On the strong unit ball, the target weighted-jet energy beyond the
Japanese-bracket radius `ρ` is at most `ρ⁻⁴`. -/
theorem fp81s21_weightedRellich_tailEnergy_unit_le
    {d q : ℕ} {P ρ : ℝ} (hρ : 1 ≤ ρ) (f : Euc d → ℝ)
    (hE : weightedSobolevE (q + 2) P f ≤ 1) :
    fp81s21_weightedRellich_tailEnergy (d := d) q (P + 2) ρ f ≤
      ENNReal.ofReal (ρ ^ (-4 : ℝ)) := by
  have hnorm : (s57pS d (q + 2) P f) ^ (1 / 2 : ℝ) ≤ 1 := by
    simpa [s57p_E_eq] using hE
  have henergy : s57pS d (q + 2) P f ≤ 1 := by
    by_contra hnot
    have hlt : (1 : ℝ≥0∞) < s57pS d (q + 2) P f := lt_of_not_ge hnot
    have hroot := ENNReal.rpow_lt_rpow hlt
      (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
    have hroot' : (1 : ℝ≥0∞) < (s57pS d (q + 2) P f) ^ (1 / 2 : ℝ) := by
      simpa using hroot
    exact (not_lt_of_ge hnorm) hroot'
  calc
    _ ≤ ENNReal.ofReal (ρ ^ (-4 : ℝ)) * s57pS d (q + 2) P f :=
      fp81s21_weightedRellich_tailEnergy_le hρ f
    _ ≤ ENNReal.ofReal (ρ ^ (-4 : ℝ)) * 1 :=
      by
        apply mul_le_mul_right
        exact henergy
    _ = ENNReal.ofReal (ρ ^ (-4 : ℝ)) := by rw [mul_one]

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_tailEnergy_unit_le

end HRS.Fp81.S21
