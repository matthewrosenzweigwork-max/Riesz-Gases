import HRS.MS.Fp81S21TimeRep4

/-! The time-section representation contract. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

local instance (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _

/-- A measurable random time-L² class with its sample-section and
weighted-test agreement, and the prescribed second-moment bound. -/
def fp81s21_TimeRep {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ) (q : ℝ → Ω → r26t6_Coeff)
    (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) : Prop :=
  Measurable U ∧ MemLp U 2 P ∧
    (∫ ω, ‖U ω‖ ^ 2 ∂P) ≤ H * M ∧
    ∀ᵐ ω ∂P,
      MemLp (fun t => q (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) H)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) H)),
        (U ω : ℝ → r26t6_Coeff) t = q (a + t) ω ∧
        ∀ f, IsR2WeightedTest r Pw f →
          fp81s21_chartAction E ((U ω : ℝ → r26t6_Coeff) t) f = Q (a + t) ω f

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_TimeRep
