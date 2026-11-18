import HRS.MS.Fp81S21GaussMomRep3

/-! A simultaneous compact-test event from samplewise chart continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- Coordinate agreement identifies a samplewise bounded linear compact-test
functional with the chart action, simultaneously on the entire test core.
The exact dual norm follows from the same Riesz representation. -/
theorem fp81s21_compact_event_of_bounded_coordinates
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Q : Ω → (Euc d → ℝ) → ℝ)
    (q : Ω → r26t6_Coeff)
    (hreg : ∀ᵐ ω ∂P,
      (∀ f g, IsR2Test f → IsR2Test g → Q ω (f + g) = Q ω f + Q ω g) ∧
      (∀ c f, IsR2Test f → Q ω (c • f) = c * Q ω f) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, IsR2Test f →
        |Q ω f| ≤ C * (weightedSobolevE r Pw f).toReal)
    (hcoord : ∀ j, ∀ᵐ ω ∂P, q ω j = Q ω (E.test j)) :
    ∀ᵐ ω ∂P,
      (∀ f, IsR2Test f → fp81s21_chartAction E (q ω) f = Q ω f) ∧
      dualNormE r Pw (Q ω) = ENNReal.ofReal ‖q ω‖ := by
  filter_upwards [hreg, ae_all_iff.mpr hcoord] with ω hω hc
  obtain ⟨ha, hs, C, hC, hb⟩ := hω
  obtain ⟨z, hz, hzc, hn⟩ :=
    fp81s21_chart_riesz_from_tests_coordinate hP E (Q ω) ha hs C hC hb
  have heq : z = q ω := by
    ext j
    exact (hzc j).trans (hc j).symm
  subst z
  exact ⟨hz, hn⟩

/-- Upgrade an every-time measurable coefficient field to `MomentRep`
when the original functional is samplewise chart-continuous at each time. -/
theorem fp81s21_MomentRep_of_bounded_coordinates
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hm : Measurable (Function.uncurry q))
    (hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M)
    (hreg : ∀ u, 0 ≤ u → ∀ᵐ ω ∂P,
      (∀ f g, IsR2Test f → IsR2Test g → Q u ω (f + g) = Q u ω f + Q u ω g) ∧
      (∀ c f, IsR2Test f → Q u ω (c • f) = c * Q u ω f) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, IsR2Test f →
        |Q u ω f| ≤ C * (weightedSobolevE r Pw f).toReal)
    (hcoord : ∀ u, 0 ≤ u → ∀ j, ∀ᵐ ω ∂P,
      q u ω j = Q u ω (E.test j)) :
    fp81s21_MomentRep E P Q q M := by
  refine ⟨hm, ?_⟩
  intro u hu
  exact ⟨(hsec u hu).1, (hsec u hu).2,
    fp81s21_compact_event_of_bounded_coordinates hP E P (Q u) (q u)
      (hreg u hu) (hcoord u hu)⟩

#print axioms fp81s21_compact_event_of_bounded_coordinates
#print axioms fp81s21_MomentRep_of_bounded_coordinates
end HRS.Fp81.S21
end
