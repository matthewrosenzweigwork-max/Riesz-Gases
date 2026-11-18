import HRS.MS.Fp81S21GaussFeature

/-!
# HRS S2.1(iii), G4: combined feature increment components

The squared norm of a combined feature increment splits into the initial
reference component and the accumulated moving-noise component.  This
identity is the algebraic first step for the weighted chart increment trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The combined feature increment has orthogonal initial and moving-noise
components. -/
theorem fp81s21_combinedFeature_increment_parts
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (s t : ℝ) (φ : Euc p.d → ℝ) :
    ‖fp81s21_combinedFeature p R hK t φ -
        fp81s21_combinedFeature p R hK s φ‖ ^ 2 =
      ‖fp81s21_initialGaussianFeature p R hK t φ -
          fp81s21_initialGaussianFeature p R hK s φ‖ ^ 2 +
        ‖movingNoiseFeature R 0 t φ - movingNoiseFeature R 0 s φ‖ ^ 2 := by
  change ‖WithLp.toLp 2
        (fp81s21_initialGaussianFeature p R hK t φ,
          movingNoiseFeature R 0 t φ) -
      WithLp.toLp 2
        (fp81s21_initialGaussianFeature p R hK s φ,
          movingNoiseFeature R 0 s φ)‖ ^ 2 = _
  rw [show WithLp.toLp 2
        (fp81s21_initialGaussianFeature p R hK t φ,
          movingNoiseFeature R 0 t φ) -
        WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK s φ,
            movingNoiseFeature R 0 s φ) =
        WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK t φ -
              fp81s21_initialGaussianFeature p R hK s φ,
            movingNoiseFeature R 0 t φ - movingNoiseFeature R 0 s φ) by
      rw [← WithLp.toLp_sub]
      rfl]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

#print axioms HRS.Fp81.S21.fp81s21_combinedFeature_increment_parts

end HRS.Fp81.S21

end
