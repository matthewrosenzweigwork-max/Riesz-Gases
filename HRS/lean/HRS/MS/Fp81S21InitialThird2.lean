import HRS.MS.Fp81S21InitialThird

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc)
open HRS.MS.R26T3

/-- Pointwise expansion of a continuous trilinear form on the actual initial response vector.
The basis order is the reversed `[eₘ, eₖ, eⱼ]` order of `S99.s99_third_apply`. -/
theorem fp81s21_initial_third_expand
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SeqL2) ℝ) (x : Euc p.d) :
    T ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
        fp81s21_initial_ellv R φ x] =
      ∑' j, ∑' k, ∑' m,
        r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x *
          T ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] := by
  simpa only [fp81s21_initial_ellv_coord R hφ F x] using
    S99.s99_third_expand T (fp81s21_initial_ellv R φ x)

#print axioms fp81s21_initial_third_expand

end HRS.Fp81.S21

end
