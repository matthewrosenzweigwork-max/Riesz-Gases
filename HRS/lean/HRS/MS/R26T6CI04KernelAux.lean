import HRS.MS.R26T6CI04Centered
import HRS.MS.ThCorrRespAux2

/-! R26-T6C.I04: pointwise Hölder estimate for the row integral. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_kernel_row_holder (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (k : Euc d → Euc d → ℝ) (x : Euc d)
    (hk : MemLp (k x) 2 mu)
    (f : Euc d → ℝ) (hf : MemLp f 2 mu) :
    Integrable (fun y => k x y * f y) mu ∧
    ‖∫ y, k x y * f y ∂mu‖ₑ ≤
      eLpNorm (k x) 2 mu * eLpNorm f 2 mu := by
  have hi : Integrable (fun y => k x y * f y) mu := hk.integrable_mul hf
  refine ⟨hi, ?_⟩
  have hkm : AEMeasurable (fun y => ‖k x y‖ₑ) mu :=
    hk.aestronglyMeasurable.enorm
  have hfm : AEMeasurable (fun y => ‖f y‖ₑ) mu :=
    hf.aestronglyMeasurable.enorm
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    (p := 2) (q := 2) Real.HolderConjugate.two_two hkm hfm
  have hk_eq : eLpNorm (k x) 2 mu =
      (∫⁻ y, ‖k x y‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hk.aestronglyMeasurable)
  have hf_eq : eLpNorm f 2 mu =
      (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hf.aestronglyMeasurable)
  calc
    ‖∫ y, k x y * f y ∂mu‖ₑ ≤
      ∫⁻ y, ‖k x y * f y‖ₑ ∂mu := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖k x y‖ₑ * ‖f y‖ₑ ∂mu := by simp only [enorm_mul]
    _ ≤ eLpNorm (k x) 2 mu * eLpNorm f 2 mu := by
      simpa only [Pi.mul_apply, hk_eq, hf_eq] using hb

end HRS.MS.R26T6C
