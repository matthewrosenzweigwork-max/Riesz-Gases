import HRS.MS.Fp81S21WickApprox7

/-! Finite-coordinate fixed-time errors lifted to time L². -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance fp81s21_wickApprox8_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_wickApprox8_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Finite-coordinate sectional squared errors lift to time-L² with the
Parseval/Fubini factor `sqrt (H * m)`. -/
theorem fp81s21_time_finite_coordinate_sqerr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q r : ℝ → Ω → r26t6_Coeff) (Mq Mr a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (hr : Measurable (Function.uncurry r))
    (hU : fp81s21_TimeL2Rep P q Mq a H U)
    (hV : fp81s21_TimeL2Rep P r Mr a H V)
    (ha : 0 ≤ a) (hH : 0 ≤ H) (m : ℕ) (ε : ℝ)
    (hsupport : ∀ u, 0 ≤ u → ∀ᵐ ω ∂P,
      fp81s21_projectField m (q u ω - r u ω) = q u ω - r u ω)
    (hcoord : ∀ u, 0 ≤ u → ∀ j ∈ Finset.range m,
      fp81s21_SqErr P (fun ω => q u ω j) (fun ω => r u ω j) ε) :
    fp81s21_SqErr P U V (Real.sqrt (H * (m : ℝ)) * ε) := by
  have hsection : ∀ u, 0 ≤ u →
      fp81s21_SqErr P (q u) (r u) (Real.sqrt (m : ℝ) * ε) := by
    intro u hu
    exact fp81s21_finite_coordinate_sqerr P (q u) (r u) m ε (hsupport u hu) (hcoord u hu)
  have htime := fp81s21_time_sqerr_of_section_sqerr P q r Mq Mr a H U V
    hq hr hU hV ha hH (Real.sqrt (m : ℝ) * ε) hsection
  simpa [Real.sqrt_mul hH, mul_assoc] using htime

#print axioms fp81s21_time_finite_coordinate_sqerr
end HRS.Fp81.S21
end
