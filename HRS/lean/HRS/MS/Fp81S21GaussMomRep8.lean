import HRS.MS.Fp81S21GaussMomRep7

/-! From a moving second-moment bound to an exact chart representation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.S111X1

theorem fp81s21_oscillator_MomentRep_of_secondMoment_bound
    {d r : ℕ} {Pw m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Z : ℝ → Ω → OscDual d m)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hm : Measurable (Function.uncurry q))
    (hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M)
    (hsecond : ∀ u, 0 ≤ u → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : Euc d → ℝ, IsR2Test f →
        MemLp (fun ω => OscDual.eval (Z u ω) f) 2 P ∧
        (∫ ω, OscDual.eval (Z u ω) f ^ 2 ∂P) ≤
          C * (weightedSobolevE r Pw f).toReal ^ 2)
    (hcoord : ∀ u, 0 ≤ u → ∀ j, ∀ᵐ ω ∂P,
      q u ω j = OscDual.eval (Z u ω) (E.test j)) :
    fp81s21_MomentRep E P (fun u ω f => OscDual.eval (Z u ω) f) q M := by
  refine ⟨hm, ?_⟩
  intro u hu
  obtain ⟨hq, hmoment⟩ := hsec u hu
  obtain ⟨C, hC, hsecond'⟩ := hsecond u hu
  have hfixed := fp81s21_oscillator_testwise_of_secondMoment_bound hP E P
    (Z u) (q u) hq C hC hsecond' (hcoord u hu)
  have hevent := fp81s21_oscillator_compact_event_of_testwise_agreement hP E P
    (Z u) (q u) hfixed
  have hbound : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ f, IsR2Test f →
      |OscDual.eval (Z u ω) f| ≤ C * (weightedSobolevE r Pw f).toReal := by
    filter_upwards [hevent] with ω hω
    exact ⟨‖q u ω‖, norm_nonneg _, hω.2⟩
  exact ⟨hq, hmoment, fp81s21_oscillator_compact_event_of_bound hP E P
    (Z u) (q u) hbound (hcoord u hu)⟩

#print axioms fp81s21_oscillator_MomentRep_of_secondMoment_bound
end HRS.Fp81.S21
end
