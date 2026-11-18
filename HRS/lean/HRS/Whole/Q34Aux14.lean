import HRS.Whole.Q34Aux13

/-!
# Packet Q34, helper file 14: nonnegativity of the integral operator
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

theorem tk_pos (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u : Euc d → ℝ} (hu : Measurable u)
    (hu2 : MemLp u 2 (withDensityReal ρ)) :
    0 ≤ ∫ x, Tk s (withDensityReal ρ) u x * u x ∂(withDensityReal ρ) := by
  have := isProbabilityMeasure_nu hρ
  have := noAtoms_nu (ρ := ρ) hd
  set ν := withDensityReal ρ with hν
  have hI := tk_pair_integrable hd hs0 hsd hρ hM hu hu hu2 hu2
  have h1 : ∫ x, Tk s ν u x * u x ∂ν =
      ∫ z, ‖z.1 - z.2‖ ^ (-s) * u z.2 * u z.1 ∂(ν.prod ν) := by
    rw [integral_prod _ hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Tk]
    rw [← integral_mul_const]
  rw [h1]
  have hI' : Integrable (fun z : Euc d × Euc d => ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2))
      (ν.prod ν) := by
    refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  have := riesz_posdef hs0 hu (hu2.integrable (by norm_num)) hI'
  refine le_of_le_of_eq this (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  simp only
  ring

end HRS.Whole.Q34
