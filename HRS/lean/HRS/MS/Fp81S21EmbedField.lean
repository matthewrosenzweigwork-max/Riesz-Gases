import HRS.MS.Fp81S21WeightedNorm
import HRS.MS.S21G2_W01

/-! Exact norm bridge between the chart and weighted ordered-jet models. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6
  HRS.MS.ProClosureS111

/-- On compact smooth tests, the chart coordinate norm and the weighted-jet
norm coincide exactly. The second conjunct records the `ℝ≥0∞` identity from
which the real norm equality follows. -/
theorem fp81s21_embedField_chartJet_norm
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (f : Euc d → ℝ) (hf : IsR2Test f) :
    ‖Es.encode f‖ = ‖r26t3_jet q (Pw + 2) f‖ ∧
      ‖r26t3_jet q (Pw + 2) f‖ₑ = weightedSobolevE q (Pw + 2) f := by
  have hwt : IsR2WeightedTest q (Pw + 2) f :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hP hf)
  have hchart := Es.norm f hwt
  have hjet := r26t3_jet_norm (Pw + 2) f hwt
  have hjet' : ENNReal.ofReal ‖r26t3_jet q (Pw + 2) f‖ =
      weightedSobolevE q (Pw + 2) f := by
    rw [ofReal_norm_eq_enorm]
    exact hjet.2
  have hreal : ‖r26t3_jet q (Pw + 2) f‖ =
      (weightedSobolevE q (Pw + 2) f).toReal := by
    calc
      ‖r26t3_jet q (Pw + 2) f‖ =
          (ENNReal.ofReal ‖r26t3_jet q (Pw + 2) f‖).toReal := by simp
      _ = (weightedSobolevE q (Pw + 2) f).toReal :=
          congrArg ENNReal.toReal hjet'
  exact ⟨hchart.trans hreal.symm, hjet.2⟩

#print axioms HRS.Fp81.S21.fp81s21_embedField_chartJet_norm

end HRS.Fp81.S21
