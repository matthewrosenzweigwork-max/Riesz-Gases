import HRS.MS.R26T8AP08b
import HRS.MS.R26T8ARow6
import HRS.MS.R26T8AP10a1
import HRS.MS.WadAux37

/-!
# S8.2 T8A P08 (part c): integrals against `withDensityReal`, polynomial decay from Gaussian jet bounds
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f25_wd_integral {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (f : Euc d → ℝ) :
    ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem r26t8a_f25_wd_integrable {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (f : Euc d → ℝ) :
    Integrable f (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun y => ρ y * f y) := by
  rw [HRS.Whole.withDensityReal, integrable_withDensity_iff_integrable_smul'
    hρ.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem r26t8a_f25_rho_poly {ρ : Euc d → ℝ} {Cρ c : ℝ} (hCρ : 0 ≤ Cρ) (hc : 0 < c) {K0 : ℕ}
    (hb : ∀ j ≤ K0, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Cρ * Real.exp (-c * ‖u‖ ^ 2)) (N : ℝ) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ j ≤ K0, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Kp * (1 + ‖u‖) ^ (-N) := by
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss N hc
  refine ⟨Cρ * Cp, by positivity, fun j hj u => ?_⟩
  refine (hb j hj u).trans ?_
  have h1 := hCp ‖u‖ (norm_nonneg _)
  have h2 : Real.exp (-(c / 2) * ‖u‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖u‖])
  have h3 : (1 + ‖u‖) ^ N * Real.exp (-c * ‖u‖ ^ 2) ≤ Cp := h1.trans (by nlinarith)
  have hpos : 0 < (1 + ‖u‖) ^ N := Real.rpow_pos_of_pos (by positivity) _
  have h4 : Real.exp (-c * ‖u‖ ^ 2) ≤ Cp * (1 + ‖u‖) ^ (-N) := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hCρ]

end HRS.MS.R26T8A
