import HRS.MS.Fp81S21WindowSup11

/-!
# HRS S2.1(iii), SOL40 packet 9d: sixth-moment norm conversion

The compiled source definition used by the initial-coordinate estimate is
`SixthBound P Y M := Integrable (fun ω => ‖Y ω‖ ^ 6) P ∧
  (∫ ω, ‖Y ω‖ ^ 6 ∂P) ≤ M`.  This adapter converts that real integral bound
into the corresponding `eLpNorm` bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A sixth-moment integral bound gives the matching `L⁶` seminorm bound. -/
theorem fp81s21_sixthBound_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (M : ℝ)
    (hYmeas : Measurable Y) (hM : 0 ≤ M)
    (hY : SixthBound P Y M) :
    eLpNorm Y (ENNReal.ofReal 6) P ≤ ENNReal.ofReal (M ^ (1 / 6 : ℝ)) := by
  have hNonneg : ∀ ω, 0 ≤ ‖Y ω‖ ^ 6 := fun ω => by positivity
  have hLfin :
      (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P) < ⊤ := by
    have h := hY.1.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hNonneg)] at h
    exact h
  have hRealToENN :
      ∫ ω, ‖Y ω‖ ^ 6 ∂P =
        (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hNonneg)
      hY.1.aestronglyMeasurable
  have hLinBound :
      (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P) ≤ ENNReal.ofReal M := by
    have hToReal :
        (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P).toReal ≤ M := by
      rw [← hRealToENN]
      exact hY.2
    calc
      _ = ENNReal.ofReal
            (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P).toReal :=
          (ENNReal.ofReal_toReal hLfin.ne).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hToReal
  have hSixthEq :
      (∫⁻ ω, ENNReal.ofReal |Y ω| ^ (6 : ℝ) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P := by
    apply lintegral_congr
    intro ω
    rw [Real.norm_eq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    rw [← ENNReal.rpow_natCast]
    rfl
  have hLpPower :
      eLpNorm Y (ENNReal.ofReal 6) P ^ (6 : ℝ) ≤ ENNReal.ofReal M := by
    rw [← HRS.MS.R2Wfm.s97_lint_eq P Y hYmeas.aestronglyMeasurable
      (r := 6) (by norm_num), hSixthEq]
    exact hLinBound
  have hRoot := ENNReal.rpow_le_rpow hLpPower (by norm_num : 0 ≤ (1 / 6 : ℝ))
  have hRootLeft :
      (eLpNorm Y (ENNReal.ofReal 6) P ^ (6 : ℝ)) ^ (1 / 6 : ℝ) =
        eLpNorm Y (ENNReal.ofReal 6) P := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hRootRight :
      (ENNReal.ofReal M) ^ (1 / 6 : ℝ) =
        ENNReal.ofReal (M ^ (1 / 6 : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)]
  rw [hRootLeft, hRootRight] at hRoot
  exact hRoot

#print axioms fp81s21_sixthBound_eLpNorm

end HRS.Fp81.S21

end
