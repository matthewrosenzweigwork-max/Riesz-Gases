import HRS.MS.Fp81S21BlockValue11

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Classical
namespace HRS.Fp81.S21

/-- Translation from unit-clock time to the corresponding physical block,
including an arbitrary measurable physical-time localization. -/
theorem fp81s21_blockValue_integral_shift
    (F : ℝ → ℝ) (S : Set ℝ) (hS : MeasurableSet S) (k : ℕ) :
    (∫ s in Icc (0 : ℝ) 1, S.indicator F ((k : ℝ) + s)) =
      ∫ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S, F v := by
  calc
    _ = ∫ v in Icc (k : ℝ) ((k : ℝ) + 1), S.indicator F v :=
      (fp81s21_window_shift_measurePreserving (k : ℝ) 1).integral_comp
        (measurableEmbedding_addLeft (k : ℝ)) (S.indicator F)
    _ = _ := setIntegral_indicator hS

#print axioms fp81s21_blockValue_integral_shift
end HRS.Fp81.S21
end
