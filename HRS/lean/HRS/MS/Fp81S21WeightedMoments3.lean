import HRS.MS.Fp81S21WeightedMoments2

/-! The Hilbert-space Riesz representation brick for the weighted chart.

This first brick starts from a continuous functional on the chart coefficient
space.  It records the exact chart action and dual norm; extending a functional
given only on compact tests is a separate step.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6

/-- A continuous functional on the coefficient Hilbert space is represented
by its Riesz vector, and its induced chart action has exactly that dual norm. -/
theorem fp81s21_chart_riesz_of_continuous
    {d r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (L : r26t6_Coeff →L[ℝ] ℝ) :
    ∃ z : r26t6_Coeff,
      (∀ f, fp81s21_chartAction E z f = L (E.encode f)) ∧
      dualNormE r Pw (fun f => L (E.encode f)) = ENNReal.ofReal ‖z‖ := by
  let z : r26t6_Coeff := (InnerProductSpace.toDual ℝ r26t6_Coeff).symm L
  have hz : InnerProductSpace.toDual ℝ r26t6_Coeff z = L := by
    exact (InnerProductSpace.toDual ℝ r26t6_Coeff).apply_symm_apply L
  have haction : ∀ f, fp81s21_chartAction E z f = L (E.encode f) := by
    intro f
    have heval := congrArg (fun F : r26t6_Coeff →L[ℝ] ℝ => F (E.encode f)) hz
    change (InnerProductSpace.toDual ℝ r26t6_Coeff z) (E.encode f) = _ at heval
    change inner ℝ z (E.encode f) = L (E.encode f)
    simpa [InnerProductSpace.toDual, InnerProductSpace.toDualMap,
      fp81s21_chartAction] using heval
  refine ⟨z, haction, ?_⟩
  have hfun : (fun f => L (E.encode f)) = fp81s21_chartAction E z := by
    funext f
    exact (haction f).symm
  rw [hfun]
  exact fp81s21_chartAction_dualNorm hP E z

#print axioms HRS.Fp81.S21.fp81s21_chart_riesz_of_continuous

end HRS.Fp81.S21
