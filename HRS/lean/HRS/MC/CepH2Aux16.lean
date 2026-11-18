import HRS.MC.CepH2Aux15

/-!
# CEPH2, helper 16: the integrated-by-parts integrand and the commutator bound

* `h2_B_leibniz`: `h2_B` depends on `φ` only through `fderiv φ x`, linearly.
* `h2_Bint_ell`: `∫ h2_B ℓ x y dμ(y) = θ Σ_k q(e_k) ∂_k u + ∫ q(∇U y) Ĝ(x-y) dμ`.
* `h2_lintegral_C_le`: `∫_cell C ≤ K² N v` for the commutator `C(x) = ∫ Ĝ(x-y) ‖∇U y - ∇U x‖² dμ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_integrable_per1_sub {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    Integrable (fun y => h2_per1 v (x - y)) μ := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  exact (integrable_const B).mono'
    ((h2_continuous_per1 hv).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => (h _).2.1)

theorem h2_B_leibniz {θ v : ℝ} {U : Ch N → ℝ} {φ χ ℓ : Ch N → ℝ} {x : Ch N} {a b : ℝ}
    (h : fderiv ℝ φ x = a • fderiv ℝ χ x + b • fderiv ℝ ℓ x) (y : Ch N) :
    h2_B θ v U φ x y = a * h2_B θ v U χ x y + b * h2_B θ v U ℓ x y := by
  have hs : ∀ (c d p : Fin N → ℝ), ∑ k, (a * c k + b * d k) * p k =
      a * ∑ k, c k * p k + b * ∑ k, d k * p k := by
    intro c d p
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold h2_B
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hs]
  ring

theorem h2_Bint_ell {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)}
    [IsFiniteMeasure μ] (hG1 : Integrable (fun y => ‖gradient U y‖) μ) (ℓ : Ch N → ℝ) (x : Ch N) :
    ∫ y, h2_B θ v U ℓ x y ∂μ = θ * ∑ k, fderiv ℝ ℓ x (h2_e k) * h2_mu1 v μ x (h2_e k) +
      ∫ y, fderiv ℝ ℓ x (gradient U y) * h2_per v (x - y) ∂μ := by
  have hi : ∀ k : Fin N, Integrable (fun y => h2_per1 v (x - y) (h2_e k)) μ := fun k => by
    have := (ContinuousLinearMap.apply ℝ ℝ (h2_e k)).integrable_comp (h2_integrable_per1_sub hv μ x)
    simpa using this
  have i1 : ∀ k : Fin N, Integrable (fun y => fderiv ℝ ℓ x (h2_e k) * h2_per1 v (x - y) (h2_e k)) μ :=
    fun k => (hi k).const_mul _
  unfold h2_B
  rw [integral_add ((integrable_finset_sum _ fun k _ => i1 k).const_mul θ)
    (h2_integrable_q_grad hv hU hG1 (fderiv ℝ ℓ x) x), integral_const_mul,
    integral_finset_sum _ fun k _ => i1 k]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  unfold h2_mu1
  rw [ContinuousLinearMap.integral_apply (h2_integrable_per1_sub hv μ x)]

theorem h2_C_nonneg {v : ℝ} (hv : 0 < v) (U : Ch N → ℝ) (μ : Measure (Ch N)) (x : Ch N) :
    0 ≤ h2_C v U μ x :=
  integral_nonneg fun y => mul_nonneg (h2_per_nonneg hv _) (sq_nonneg _)

theorem h2_measurable_C {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (μ : Measure (Ch N))
    [SFinite μ] : Measurable (h2_C v U μ) := by
  have hgc := h2_continuous_gradient hU
  have hc : Continuous (Function.uncurry fun x y : Ch N => h2_per v (x - y) * ‖gradient U y - gradient U x‖ ^ 2) :=
    ((h2_continuous_per hv).comp (continuous_fst.sub continuous_snd)).mul
      (((hgc.comp continuous_snd).sub (hgc.comp continuous_fst)).norm.pow 2)
  exact (hc.stronglyMeasurable.integral_prod_right (ν := μ)).measurable

theorem h2_lintegral_C_le {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_C v U μ x) ≤ ENNReal.ofReal ((K : ℝ) ^ 2 * (N * v)) := by
  have hgc := h2_continuous_gradient hU
  have e1 : ∀ x, ENNReal.ofReal (h2_C v U μ x) =
      ∫⁻ y, ENNReal.ofReal (h2_per v (x - y)) * ENNReal.ofReal (‖gradient U y - gradient U x‖ ^ 2) ∂μ := by
    intro x
    unfold h2_C
    rw [ofReal_integral_eq_lintegral_ofReal (h2_integrable_comm hv hU hG2 x)
      (ae_of_all _ fun y => mul_nonneg (h2_per_nonneg hv _) (sq_nonneg _))]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (h2_per_nonneg hv _)]
  simp_rw [e1]
  have hW : Measurable (Function.uncurry fun x y : Ch N => ENNReal.ofReal (‖gradient U y - gradient U x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((((hgc.comp continuous_snd).sub (hgc.comp continuous_fst)).norm.pow 2).measurable)
  rw [h2_lintegral_cell_mu hv μ (W := fun x y => ENNReal.ofReal (‖gradient U y - gradient U x‖ ^ 2)) hW
    (fun x y => by simp only [h2_gradient_periodic hUper])]
  have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  calc ∫⁻ y, (∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * ENNReal.ofReal (‖gradient U y - gradient U x‖ ^ 2)) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal ((K : ℝ) ^ 2 * (N * v)) ∂μ := by
        refine lintegral_mono fun y => ?_
        calc ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * ENNReal.ofReal (‖gradient U y - gradient U x‖ ^ 2)
            ≤ ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * ENNReal.ofReal (0 + (K : ℝ) ^ 2 * ‖x - y‖ ^ 2) := by
              refine lintegral_mono fun x => ?_
              refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
              have := h2_grad_commutator hUper hK x y 0
              simp only [Int.cast_zero, zero_smul, add_zero] at this
              rw [zero_add, ← mul_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) this 2
          _ = ∫⁻ z, ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (0 + (K : ℝ) ^ 2 * ‖z‖ ^ 2) := by
              have := h2_lintegral_gauss_shift (v := v) (fun x => ENNReal.ofReal (0 + (K : ℝ) ^ 2 * ‖x - y‖ ^ 2)) y
              simpa using this
          _ = ENNReal.ofReal (0 + (K : ℝ) ^ 2 * (N * v)) := h2_lintegral_gauss_poly hv 0 _ le_rfl hK2
          _ = _ := by rw [zero_add]
    _ = ENNReal.ofReal ((K : ℝ) ^ 2 * (N * v)) := by simp

theorem h2_integrableOn_C {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) :
    IntegrableOn (h2_C v U μ) (cep_cell N) := by
  refine ⟨(h2_measurable_C hv hU μ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => h2_C_nonneg hv U μ x)]
  exact lt_of_le_of_lt (h2_lintegral_C_le hv hU hUper hK μ hG2) ENNReal.ofReal_lt_top

theorem h2_integral_C_le {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) :
    ∫ x in cep_cell N, h2_C v U μ x ≤ (K : ℝ) ^ 2 * (N * v) := by
  have h := ofReal_integral_eq_lintegral_ofReal (h2_integrableOn_C hv hU hUper hK μ hG2)
    (ae_of_all _ fun x => h2_C_nonneg hv U μ x)
  have h2 := h2_lintegral_C_le hv hU hUper hK μ hG2
  rw [← h] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end HRS.MC.CepH2
