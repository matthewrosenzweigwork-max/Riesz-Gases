import HRS.MC.CepH2Init1

/-!
# CEPH2, C4 (b): the potential term of the mollified free energy
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_amgm {g w η : ℝ} (hη : 0 < η) : g * w ≤ η / 2 * g ^ 2 + 1 / (2 * η) * w ^ 2 := by
  have h : η / 2 * g ^ 2 + 1 / (2 * η) * w ^ 2 - g * w = (η * g - w) ^ 2 / (2 * η) := by
    field_simp
    ring
  have : 0 ≤ (η * g - w) ^ 2 / (2 * η) := by positivity
  linarith

theorem h2_U_term {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) {C : ℝ} (hC : ∀ z, 0 ≤ U z + C) {v : ℝ} (hv : 0 < v) {η : ℝ}
    (hη : 0 < η) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    (hUC : Integrable (fun y => U y + C) μ) (hG : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) :
    Integrable (fun x => h2_mu v μ x * (U x + C)) (volume.restrict (cep_cell N)) ∧
    ∫ x in cep_cell N, h2_mu v μ x * (U x + C) ≤
      ∫ y, (U y + C) ∂μ + η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂μ + ((K : ℝ) / 2 + 1 / (2 * η)) * (N * v) := by
  set b : ℝ := (K : ℝ) / 2 + 1 / (2 * η) with hb
  have hb0 : 0 ≤ b := by positivity
  set φ : Ch N → ℝ := fun y => U y + C + η / 2 * ‖gradient U y‖ ^ 2 with hφ
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => by have := hC y; simp only [hφ]; positivity
  have hUm : Measurable fun x => ENNReal.ofReal (U x + C) :=
    ENNReal.measurable_ofReal.comp ((hU.continuous.add continuous_const).measurable)
  have hle : ∀ x y, ENNReal.ofReal (U x + C) ≤ ENNReal.ofReal (φ y + b * ‖x - y‖ ^ 2) := by
    intro x y
    refine ENNReal.ofReal_le_ofReal ?_
    have hq := (abs_le.1 (h2_U_quad hU hK y (x - y))).2
    rw [add_sub_cancel] at hq
    have hi : inner ℝ (gradient U y) (x - y) ≤ ‖gradient U y‖ * ‖x - y‖ := real_inner_le_norm _ _
    have ha := h2_amgm (g := ‖gradient U y‖) (w := ‖x - y‖) hη
    simp only [hφ, hb]
    nlinarith [hq, hi, ha]
  have hT := h2_moment_transfer hv μ hUm (fun x => by rw [hUper]) hφ0 hb0 hle
  have hint : Integrable (fun y => φ y + b * (N * v)) μ :=
    (hUC.add (hG.const_mul (η / 2))).add (integrable_const _)
  have hR : ∫⁻ y, ENNReal.ofReal (φ y + b * (N * v)) ∂μ = ENNReal.ofReal (∫ y, (φ y + b * (N * v)) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by have := hφ0 y; positivity)).symm
  have hu0 : ∀ x, 0 ≤ h2_mu v μ x := fun x => (h2_mu_pos hv μ x).le
  have hnn : ∀ x, 0 ≤ h2_mu v μ x * (U x + C) := fun x => mul_nonneg (hu0 x) (hC x)
  have hconv : ∀ x, ENNReal.ofReal (h2_mu v μ x * (U x + C)) = ENNReal.ofReal (h2_mu v μ x) * ENNReal.ofReal (U x + C) :=
    fun x => ENNReal.ofReal_mul (hu0 x)
  have hmeas : AEStronglyMeasurable (fun x => h2_mu v μ x * (U x + C)) (volume.restrict (cep_cell N)) :=
    ((h2_continuous_mu hv μ).mul (hU.continuous.add continuous_const)).aestronglyMeasurable
  have hfin : ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_mu v μ x * (U x + C)) ≤ ENNReal.ofReal (∫ y, (φ y + b * (N * v)) ∂μ) := by
    simp_rw [hconv]
    rw [← hR]; exact hT
  have hI : Integrable (fun x => h2_mu v μ x * (U x + C)) (volume.restrict (cep_cell N)) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)
  have h3 : ENNReal.ofReal (∫ x in cep_cell N, h2_mu v μ x * (U x + C)) ≤
      ENNReal.ofReal (∫ y, (φ y + b * (N * v)) ∂μ) := by rw [h1]; exact hfin
  have h2 := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun y => by have := hφ0 y; positivity)).1 h3
  have e : ∫ y, (φ y + b * (N * v)) ∂μ = ∫ y, (U y + C) ∂μ + η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂μ + b * (N * v) := by
    have hA : Integrable (fun y => U y + C + η / 2 * ‖gradient U y‖ ^ 2) μ := hUC.add (hG.const_mul _)
    have hB : Integrable (fun y => η / 2 * ‖gradient U y‖ ^ 2) μ := hG.const_mul _
    simp only [hφ]
    rw [integral_add hA (integrable_const _), integral_add hUC hB, integral_const_mul]
    simp
  rw [e] at h2
  exact h2

end HRS.MC.CepH2
