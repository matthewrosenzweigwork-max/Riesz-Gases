import HRS.MS.SA16Y4Ct1
import HRS.MS.SA16Y3Ex2

/-!
# S.A.16 (SA16Y4) Ct2: pointwise bound `|f - ρ_n ⋆ f| ≤ ∫ ρ_n(y)‖y‖ ∫_0^1 G(x - s y) ds dy` (as `ℝ≥0∞` integrals)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Ct2
variable {d : ℕ}

lemma sa16y4_sub_pt {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖f x - sa16q_mol n f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (sa16y_rho d n y * ‖y‖) *
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (sa16y4_G1 f (x - s • y)) := by
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d n z := sa16y_rho_nonneg n
  have hρ1 := sa16y_rho_int (d := d) n
  have e1 : f x - sa16q_mol n f x = ∫ z, sa16y_rho d n z * (f x - f (x - z)) := by
    have hi1 : Integrable (fun z => sa16y_rho d n z * f x) := (sa16y_rho_integrable n).mul_const _
    have hi2 : Integrable (fun z => sa16y_rho d n z * f (x - z)) := sa16y3_mol_integrable n hf x
    have : ∫ z, sa16y_rho d n z * (f x - f (x - z)) =
        (∫ z, sa16y_rho d n z * f x) - ∫ z, sa16y_rho d n z * f (x - z) := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [this, integral_mul_const, hρ1, one_mul]
    rfl
  rw [e1]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [enorm_mul, Real.enorm_eq_ofReal (hρ0 z), ENNReal.ofReal_mul (hρ0 z)]
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [sa16y4_seg_ftc hf x z, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - s • z) z‖ₑ
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ‖z‖ * ENNReal.ofReal (sa16y4_G1 f (x - s • z)) := by
        refine lintegral_mono fun s => ?_
        rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (sa16y4_fderiv_le _ _)
    _ = ENNReal.ofReal ‖z‖ * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (sa16y4_G1 f (x - s • z)) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

end Ct2

end HRS.Whole.AppendixA.Phase2SA16R
