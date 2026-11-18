import HRS.MS.Fp81S21WickMomRep
import HRS.MS.Fp81S21WeightedMoments2
import HRS.MS.Fp81S21WeightedNorm

/-! Coherent chart action and its exact moment representation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- The coherent field associated with a coefficient representative. -/
def fp81s21_wickChartField {d r : ℕ} {Pw : ℝ} {Ω : Type*}
    (E : r26t6_WeightedChart d r Pw) (q : ℝ → Ω → r26t6_Coeff) :
    ℝ → Ω → (Euc d → ℝ) → ℝ :=
  fun u ω => fp81s21_chartAction E (q u ω)

/-- The chart action has the exact dual norm on every sample. This result
is independent of the separate identification with the half-Wick operator. -/
theorem fp81s21_wickChartField_momentRep
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hm : Measurable (Function.uncurry q))
    (hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M) :
    fp81s21_MomentRep E P (fp81s21_wickChartField E q) q M := by
  refine ⟨hm, fun u hu => ⟨(hsec u hu).1, (hsec u hu).2, ?_⟩⟩
  exact Filter.Eventually.of_forall fun ω =>
    ⟨fun _ _ => rfl, fp81s21_chartAction_dualNorm hP E (q u ω)⟩

/-- First dual-norm moment of the coherent chart field. -/
theorem fp81s21_wickChartField_firstMoment
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hm : Measurable (Function.uncurry q))
    (hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M) (u : ℝ) (hu : 0 ≤ u) :
    AEMeasurable (fun ω => dualNormE r Pw (fp81s21_wickChartField E q u ω)) P ∧
      (∫⁻ ω, dualNormE r Pw (fp81s21_wickChartField E q u ω) ∂P) ≤
        ENNReal.ofReal (Real.sqrt M) :=
  fp81s21_MomentRep_firstMoment E P _ q M
    (fp81s21_wickChartField_momentRep hP E P q M hm hsec) u hu

#print axioms fp81s21_wickChartField_momentRep
#print axioms fp81s21_wickChartField_firstMoment
end HRS.Fp81.S21
end
