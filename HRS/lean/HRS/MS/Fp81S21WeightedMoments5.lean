import HRS.MS.Fp81S21WeightedMoments4

/-! The chart coordinates of the Riesz representative are test values. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6

/-- The Riesz coefficient at chart coordinate `j` is the functional's
value on the corresponding chart test. -/
theorem fp81s21_chart_riesz_from_tests_coordinate
    {d r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (T : (Euc d → ℝ) → ℝ)
    (hadd : ∀ f g, IsR2Test f → IsR2Test g →
      T (f + g) = T f + T g)
    (hsmul : ∀ c f, IsR2Test f → T (c • f) = c * T f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f, IsR2Test f →
      |T f| ≤ C * (weightedSobolevE r Pw f).toReal) :
    ∃ z : r26t6_Coeff,
      (∀ f, IsR2Test f → fp81s21_chartAction E z f = T f) ∧
      (∀ j, z j = T (E.test j)) ∧
      dualNormE r Pw T = ENNReal.ofReal ‖z‖ := by
  obtain ⟨z, haction, hnorm⟩ :=
    fp81s21_chart_riesz_from_tests hP E T hadd hsmul C hC hbound
  refine ⟨z, haction, ?_, hnorm⟩
  intro j
  have hcoord : E.encode (E.test j) = (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  have h := haction (E.test j) (E.test_smooth j)
  rw [fp81s21_chartAction, hcoord] at h
  simpa [lp.inner_single_right] using h

#print axioms HRS.Fp81.S21.fp81s21_chart_riesz_from_tests_coordinate

end HRS.Fp81.S21
