import HRS.MS.Fp81S21WeightedNorm
import HRS.MS.S21F_D00

/-!
# S2.1(iii), packet 32b B3: weighted generator contract

This file currently records the exact contract header only.  The missing analytic
step is the uniform weighted Sobolev estimate for the full moving generator,
including its nonlocal convolution term.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Statement-only B3 contract, with the common physical radius and joint
measurability made explicit.  The operator may depend on the trajectory and on
the two chosen charts; the nonnegative bound is chosen uniformly before those
inputs and before time. -/
def fp81s21_weightedGen_contract (p : Parameters) : Prop :=
  ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ (1 / 2 : ℝ) ∧
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
    ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∃ L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff,
        Measurable (fun q : ℝ × r26t6_Coeff => L q.1 q.2) ∧
        (∀ u : ℝ, 0 ≤ u → ‖L u‖ ≤ C) ∧
        ∀ u : ℝ, 0 ≤ u → ∀ z f,
          IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
          IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
            (generatorW (r26t3_coeff R) u f) ∧
          weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (generatorW (r26t3_coeff R) u f) ≤
            ENNReal.ofReal C *
              weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2) f ∧
          fp81s21_chartAction E (L u z) f =
            fp81s21_chartAction Es z (generatorW (r26t3_coeff R) u f)

#print axioms fp81s21_weightedGen_contract

end HRS.Fp81.S21
