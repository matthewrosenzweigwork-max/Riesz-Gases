import HRS.MS.Fp81S21TimeRep11
import HRS.MS.Fp81S21RankKernel

/-! Quantitative projection tails for time-section classes. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Fixed-time projection tail moments lift to time-L² squared-error and
Markov bounds. -/
theorem fp81s21_time_projection_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hcore : fp81s21_TimeL2Rep P q M a H U)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 ≤ ε m)
    (htail : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2) P ∧
      (∫ ω, ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2 ∂P) ≤ M * (ε m) ^ 2) :
    ∀ m, fp81s21_SqErr P U (fun ω => fp81s21_timeProject H m (U ω))
        (Real.sqrt (H * M) * ε m) ∧
      ∀ ρ : ℝ, 0 < ρ →
        P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
          ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2) := by
  intro m
  obtain ⟨hi, hb⟩ := fp81s21_time_projection_second_moment P q M a H U hq hcore ha hH m (ε m) (htail m)
  refine ⟨⟨hi, ?_⟩, ?_⟩
  · rw [mul_pow, Real.sq_sqrt (mul_nonneg hH hM)]
    exact hb
  · intro ρ hρ
    have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    have hmark := (hi.div_const (ρ ^ 2)).measure_le_integral
      (ae_of_all P fun ω => div_nonneg (sq_nonneg _) hρ2.le)
      (s := {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖}) (by
        intro ω hω
        apply (le_div_iff₀ hρ2).2
        change ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖ at hω
        have hn : 0 ≤ ‖U ω - fp81s21_timeProject H m (U ω)‖ := norm_nonneg _
        nlinarith)
    calc
      _ ≤ ENNReal.ofReal (∫ ω, ‖U ω - fp81s21_timeProject H m (U ω)‖ ^ 2 / ρ ^ 2 ∂P) := hmark
      _ = ENNReal.ofReal ((∫ ω, ‖U ω - fp81s21_timeProject H m (U ω)‖ ^ 2 ∂P) / ρ ^ 2) := by rw [integral_div]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hb hρ2.le)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_time_projection_tails
