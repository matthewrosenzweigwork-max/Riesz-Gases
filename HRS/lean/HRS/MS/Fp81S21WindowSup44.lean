import HRS.MS.Fp81S21WindowSup43

/-! Convert a sixth-moment slice into the scalar ENNReal root bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A sixth-moment estimate controls its ENNReal sixth root; measurability of
the original scalar is not needed because the sixth power is integrable. -/
theorem fp81s21_sixthBound_lintegral_root
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M) (hY : SixthBound P Y M) :
    (∫⁻ ω, ENNReal.ofReal |Y ω| ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
      ENNReal.ofReal (M ^ (1 / 6 : ℝ)) := by
  have hEq : (∫⁻ ω, ENNReal.ofReal |Y ω| ^ (6 : ℝ) ∂P) =
      ENNReal.ofReal (∫ ω, ‖Y ω‖ ^ 6 ∂P) := by
    have h := ofReal_integral_eq_lintegral_ofReal hY.1
      (Filter.Eventually.of_forall fun ω => show 0 ≤ ‖Y ω‖ ^ 6 by positivity)
    rw [h]
    apply lintegral_congr
    intro ω
    rw [Real.norm_eq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast]
    norm_num
  rw [hEq]
  calc
    _ ≤ (ENNReal.ofReal M) ^ (1 / 6 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hY.2) (by norm_num)
    _ = ENNReal.ofReal (M ^ (1 / 6 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg hM (by norm_num : (0 : ℝ) ≤ 1 / 6)

#print axioms fp81s21_sixthBound_lintegral_root
end HRS.Fp81.S21
end
