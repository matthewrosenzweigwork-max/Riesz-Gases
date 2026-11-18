import HRS.MC.CepH2Aux8

/-!
# CEPH2, helper 9: mass, moments and logarithmic bounds of the mollified density
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_measurable_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] :
    Measurable (h2_mu v μ) :=
  (continuous_iff_continuousAt.2 fun x => (h2_hasFDerivAt_mu hv μ x).continuousAt).measurable

theorem h2_continuous_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] :
    Continuous (h2_mu v μ) :=
  continuous_iff_continuousAt.2 fun x => (h2_hasFDerivAt_mu hv μ x).continuousAt

/-- Mass of the mollified density on the cell. -/
theorem h2_lintegral_cell_mu_one {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_mu v μ x) = 1 := by
  have := h2_lintegral_cell_mu_weight hv μ (w := fun _ => 1) measurable_const (fun _ => rfl)
  simp only [mul_one] at this
  rw [this]
  have h1 : ∀ y : Ch N, ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) = 1 := fun y => by
    have := h2_lintegral_gauss_shift (v := v) (fun _ => (1 : ℝ≥0∞)) y
    simp only [mul_one] at this
    rw [this]
    have h := h2_lintegral_gauss_poly (N := N) hv 1 0 zero_le_one le_rfl
    simpa using h
  simp [h1]

theorem h2_integrableOn_cell_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    IntegrableOn (h2_mu v μ) (cep_cell N) := by
  refine ⟨(h2_continuous_mu hv μ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (h2_mu_pos hv μ x).le)]
  rw [h2_lintegral_cell_mu_one hv μ]; exact ENNReal.one_lt_top

theorem h2_integral_cell_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    ∫ x in cep_cell N, h2_mu v μ x = 1 := by
  have := ofReal_integral_eq_lintegral_ofReal (h2_integrableOn_cell_mu hv μ)
    (ae_of_all _ fun x => (h2_mu_pos hv μ x).le)
  rw [h2_lintegral_cell_mu_one hv μ] at this
  have h0 : 0 ≤ ∫ x in cep_cell N, h2_mu v μ x := setIntegral_nonneg h2_cell_measurable fun x _ => (h2_mu_pos hv μ x).le
  rwa [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one] at this

/-- Transfer of moments from `μ` to the mollified density. -/
theorem h2_moment_transfer {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    {w : Ch N → ℝ≥0∞} (hw : Measurable w) (hper : ∀ x, w (x + cep_diag N) = w x)
    {φ : Ch N → ℝ} (hφ : ∀ y, 0 ≤ φ y) {b : ℝ} (hb : 0 ≤ b)
    (hle : ∀ x y, w x ≤ ENNReal.ofReal (φ y + b * ‖x - y‖ ^ 2)) :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_mu v μ x) * w x ≤ ∫⁻ y, ENNReal.ofReal (φ y + b * (N * v)) ∂μ := by
  rw [h2_lintegral_cell_mu_weight hv μ hw hper]
  refine lintegral_mono fun y => ?_
  calc ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * w x
      ≤ ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * ENNReal.ofReal (φ y + b * ‖x - y‖ ^ 2) :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hle x y)
    _ = ∫⁻ z, ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (φ y + b * ‖z‖ ^ 2) := by
        rw [← lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (φ y + b * ‖z‖ ^ 2)) y]
    _ = ENNReal.ofReal (φ y + b * (N * v)) := h2_lintegral_gauss_poly hv _ _ (hφ y) hb

theorem h2_sq_perp_le (x y : Ch N) : ‖h2_perp x‖ ^ 2 ≤ 2 * ‖h2_perp y‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
  have h1 : ‖h2_perp x‖ ≤ ‖h2_perp y‖ + ‖x - y‖ := by
    have : h2_perp x = h2_perp y + h2_perp (x - y) := by
      rw [← h2_perp_add]; congr 1; abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (h2_norm_perp_le _))
  nlinarith [sq_nonneg (‖h2_perp y‖ - ‖x - y‖), norm_nonneg (h2_perp x), norm_nonneg (h2_perp y), norm_nonneg (x - y)]

end HRS.MC.CepH2
