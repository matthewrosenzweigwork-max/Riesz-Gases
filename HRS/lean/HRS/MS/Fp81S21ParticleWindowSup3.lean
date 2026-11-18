import HRS.MS.Fp81S21ParticleWindowSup2
import HRS.MS.Fp81S21WindowSupMeas3

/-! Moment-to-Lp conversions for modewise window bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A sixth-moment bound gives the corresponding `L⁶` seminorm bound. -/
theorem fp81s21_moment6_eLpNorm'_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hY : fp81s21_Moment6 P Y (M ^ 6)) :
    eLpNorm' Y 6 P ≤ ENNReal.ofReal M := by
  rcases hY with ⟨hYm, hYi, hYb⟩
  have hnonneg : 0 ≤ᵐ[P] fun ω => ‖Y ω‖ ^ 6 :=
    Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg _) _
  have hconv := ofReal_integral_eq_lintegral_ofReal hYi hnonneg
  have hfun : (fun ω => ENNReal.ofReal (‖Y ω‖ ^ 6)) =
      (fun ω => ‖Y ω‖ₑ ^ (6 : ℝ)) := by
    funext ω
    simp [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_pow]
  have hInt : (∫⁻ ω, ‖Y ω‖ₑ ^ (6 : ℝ) ∂P) ≤ ENNReal.ofReal (M ^ 6) := by
    calc
      (∫⁻ ω, ‖Y ω‖ₑ ^ (6 : ℝ) ∂P) = ENNReal.ofReal (∫ ω, ‖Y ω‖ ^ 6 ∂P) := by
        calc
          (∫⁻ ω, ‖Y ω‖ₑ ^ (6 : ℝ) ∂P) =
              ∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P := by
                apply lintegral_congr_ae
                exact Filter.Eventually.of_forall fun ω => (congrFun hfun ω).symm
          _ = ENNReal.ofReal (∫ ω, ‖Y ω‖ ^ 6 ∂P) := hconv.symm
      _ ≤ ENNReal.ofReal (M ^ 6) := ENNReal.ofReal_le_ofReal hYb
  rw [eLpNorm'_eq_lintegral_enorm, one_div,
    ← ENNReal.le_rpow_inv_iff (by norm_num : 0 < (6 : ℝ)⁻¹), inv_inv]
  simpa [ENNReal.rpow_natCast, ENNReal.ofReal_pow hM] using hInt

#print axioms HRS.Fp81.S21.fp81s21_moment6_eLpNorm'_bound
end HRS.Fp81.S21
end
