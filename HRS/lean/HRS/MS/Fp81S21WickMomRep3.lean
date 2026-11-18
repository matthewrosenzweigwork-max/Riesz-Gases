import HRS.MS.Fp81S21WickMomRep2
import HRS.MS.Fp81S21EmbedMom3

/-! Contractive transport of the coherent chart field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- A coherent chart field and its embedded representative have the same
second-moment constant and the same first dual-norm moment estimate. -/
theorem fp81s21_wickChartField_embedded
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d r (Pw + 2))
    (E : r26t6_WeightedChart d (r + 2) Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hm : Measurable (Function.uncurry q))
    (hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M) :
    fp81s21_MomentRep Es P (fp81s21_wickChartField Es q) q M ∧
    fp81s21_MomentRep E P (fp81s21_wickChartField Es q)
      (fun u ω => fp81s21_embedField hP hPs Es E (q u ω)) M ∧
    ∀ u, 0 ≤ u →
      (AEMeasurable (fun ω => dualNormE r (Pw + 2)
        (fp81s21_wickChartField Es q u ω)) P ∧
        (∫⁻ ω, dualNormE r (Pw + 2) (fp81s21_wickChartField Es q u ω) ∂P) ≤
          ENNReal.ofReal (Real.sqrt M)) ∧
      (AEMeasurable (fun ω => dualNormE (r + 2) Pw
        (fp81s21_wickChartField Es q u ω)) P ∧
        (∫⁻ ω, dualNormE (r + 2) Pw (fp81s21_wickChartField Es q u ω) ∂P) ≤
          ENNReal.ofReal (Real.sqrt M)) := by
  have hs := fp81s21_wickChartField_momentRep hPs Es P q M hm hsec
  have hw := fp81s21_MomentRep_embedField hP hPs Es E P
    (fp81s21_wickChartField Es q) q M hs
  refine ⟨hs, hw, fun u hu => ⟨?_, ?_⟩⟩
  · exact fp81s21_MomentRep_firstMoment Es P _ q M hs u hu
  · exact fp81s21_MomentRep_firstMoment E P _ _ M hw u hu

#print axioms fp81s21_wickChartField_embedded
end HRS.Fp81.S21
end
