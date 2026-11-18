import HRS.MH.ConventionHolder1
import HRS.Duality.PairingExpansion
import HRS.Kernel.GradD1

/-!
# `integrable_convGradConv_integrand_of_holder`

Relocation of `HRS.integrable_convGradConv_integrand_of_holder`.  A Hölder density
(`PDE.MFHolder.Hol0 α`) gives the increment bound `|ρ(x-z) - ρ x| ≤ Λ ‖z‖^α`, and
`HRS.Duality.integrable_conv_form` (template in `HRS/Duality/PairingExpansion.lean`) gives the
integrability for a `KernelGrad.GoodKernel`, which `periodicRieszGrad` is for `1 ≤ d`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.ConventionHolder

variable {d : ℕ}

/-- Extraction of the bound and the Hölder constant of a `Hol0` function. -/
theorem ch_hol_data {α : ℝ} {ρ : Torus d → ℝ} (hρ : PDE.MFHolder.Hol0 α ρ) :
    ∃ B Λ : ℝ, 0 ≤ B ∧ 0 ≤ Λ ∧ (∀ x, |ρ x| ≤ B) ∧
      ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Λ * ‖z‖ ^ α := by
  obtain ⟨B, hB0, hB⟩ := hρ.bdd
  obtain ⟨hc, M, hM⟩ := hρ
  refine ⟨B, |M|, hB0, abs_nonneg M, hB, fun x z _ => ?_⟩
  have h1 := hM (x - z) x
  rw [sub_sub_cancel_left, norm_neg] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg (norm_nonneg _) _))

theorem integrable_convGradConv_integrand_of_holder_proof :
    type_of% @HRS.integrable_convGradConv_integrand_of_holder := by
  intro d s α hd hs0 hsd hα0 hα1 hα ρ hρ x
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  obtain ⟨B, Λ, hB0, hΛ0, hB, hH⟩ := ch_hol_data hρ
  exact Duality.integrable_conv_form hG hρ.1.measurable hB hB0 hΛ0 hα0 hα hH x

end HRS.MH.ConventionHolder
