import HRS.MC.CepH2Mom1
import HRS.Appendix.B15BDV

/-!
# CEPH2, S2a (part 2): finite cylinder entropy gives the cell support and the transverse second moment
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_cell_volume_pos : 0 < (volume : Measure (Ch N)) (cep_cell N) := by
  have hc : Continuous fun z : Ch N => z 0 := (EuclideanSpace.proj (0 : Fin N)).continuous
  have ho : IsOpen {z : Ch N | z 0 ∈ Ioo (0 : ℝ) 1} := isOpen_Ioo.preimage hc
  have hne : {z : Ch N | z 0 ∈ Ioo (0 : ℝ) 1}.Nonempty := by
    refine ⟨WithLp.toLp 2 fun _ => 1 / 2, ?_⟩
    show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1
    constructor <;> norm_num
  refine lt_of_lt_of_le (ho.measure_pos _ hne) (measure_mono fun z hz => ?_)
  exact ⟨hz.1.le, hz.2⟩

/-- Finiteness of exponential moments of the transverse variable against the Gibbs weight. -/
theorem h2_weight_exp_finite {U : Ch N → ℝ}
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ →
      ∫⁻ z in cep_cell N, ENNReal.ofReal (Real.exp (-(U z) / θ + κ * ‖h2_perp z‖ ^ 2)) < ⊤ := by
  obtain ⟨c, C, hc, h⟩ := h2_U_lower hconf
  refine ⟨c / (2 * θ), by positivity, fun κ hκ0 hκ => ?_⟩
  have ha : 0 < c / (2 * θ) := by positivity
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := Real.exp (C / θ)))
    (h2_lintegral_cell_gauss (N := N) ha))
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 := h z
  have h2 : -(U z) / θ ≤ (-(c * ‖h2_perp z‖ ^ 2 - C)) / θ :=
    div_le_div_of_nonneg_right (neg_le_neg h1) hθ.le
  have h3 : (-(c * ‖h2_perp z‖ ^ 2 - C)) / θ = -(c / θ) * ‖h2_perp z‖ ^ 2 + C / θ := by
    field_simp; ring
  have h4 : κ * ‖h2_perp z‖ ^ 2 ≤ c / (2 * θ) * ‖h2_perp z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hκ (sq_nonneg _)
  have h5 : c / θ = 2 * (c / (2 * θ)) := by field_simp
  nlinarith [h2, h3, h4, h5]

theorem h2_partition_lt_top {U : Ch N → ℝ}
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) : cep_cylPartition θ U < ⊤ := by
  obtain ⟨κ₀, hκ₀, h⟩ := h2_weight_exp_finite hconf hθ
  have := h 0 le_rfl hκ₀.le
  simpa [cep_cylPartition, cep_cylWeight] using this

theorem h2_partition_pos {U : Ch N → ℝ} (hU : Continuous U) (θ : ℝ) : 0 < cep_cylPartition θ U := by
  unfold cep_cylPartition
  rw [pos_iff_ne_zero]
  intro h0
  have hm : Measurable (cep_cylWeight θ U) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((hU.neg).div_const θ)).measurable
  rw [lintegral_eq_zero_iff hm] at h0
  have h1 : ∀ᵐ z ∂(volume.restrict (cep_cell N)), False := by
    filter_upwards [h0] with z hz
    simp [cep_cylWeight] at hz
    exact absurd hz (not_le.2 (Real.exp_pos _))
  rw [ae_iff] at h1
  simp at h1
  exact h2_cell_volume_pos.ne' (by simpa [Measure.restrict_apply_univ] using h1)

end HRS.MC.CepH2
