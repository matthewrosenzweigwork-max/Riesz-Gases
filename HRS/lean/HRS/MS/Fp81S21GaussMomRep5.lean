import HRS.MS.Fp81S21GaussMomRep4

/-! Isolating the weighted continuity needed for oscillator observations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.S111X1

/-- Oscillator evaluation is linear on the compact smooth test core.
Thus a samplewise weighted bound is the only extra regularity needed to
turn simultaneous coordinate agreement into the full compact-test event. -/
theorem fp81s21_oscillator_compact_event_of_bound
    {d r : ℕ} {Pw m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Z : Ω → OscDual d m) (q : Ω → r26t6_Coeff)
    (hbound : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ f, IsR2Test f →
      |OscDual.eval (Z ω) f| ≤ C * (weightedSobolevE r Pw f).toReal)
    (hcoord : ∀ j, ∀ᵐ ω ∂P, q ω j = OscDual.eval (Z ω) (E.test j)) :
    ∀ᵐ ω ∂P,
      (∀ f, IsR2Test f → fp81s21_chartAction E (q ω) f =
        OscDual.eval (Z ω) f) ∧
      dualNormE r Pw (fun f => OscDual.eval (Z ω) f) = ENNReal.ofReal ‖q ω‖ := by
  apply fp81s21_compact_event_of_bounded_coordinates hP E P
    (fun ω f => OscDual.eval (Z ω) f) q _ hcoord
  filter_upwards [hbound] with ω hb
  refine ⟨?_, ?_, hb⟩
  · intro f g hf hg
    let f' : oscSub d m := ⟨f, r2Test_isOscTest m hf⟩
    let g' : oscSub d m := ⟨g, r2Test_isOscTest m hg⟩
    simpa only [gaussianTestEvaluation_apply, Submodule.coe_add, f', g'] using
      (map_add (gaussianTestEvaluation (Z ω)) f' g')
  · intro c f hf
    let f' : oscSub d m := ⟨f, r2Test_isOscTest m hf⟩
    simpa only [gaussianTestEvaluation_apply, Submodule.coe_smul, smul_eq_mul, f'] using
      (map_smul (gaussianTestEvaluation (Z ω)) c f')

#print axioms fp81s21_oscillator_compact_event_of_bound
end HRS.Fp81.S21
end
