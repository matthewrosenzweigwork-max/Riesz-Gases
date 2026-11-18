import HRS.MC.CepH2Aux26

/-!
# CEPH2, helper 27: the dominating kernel `Ω_R` is integrable and its tail vanishes
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The dominating kernel. -/
def h2_Om (v a₁ b₁ R : ℝ) (x y : Ch N) : ℝ≥0∞ :=
  ENNReal.ofReal (h2_per (2 * v) (x - y)) *
    ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)))

/-- Explicit constants of the bound. -/
def h2_A2 (N : ℕ) (v a₁ b₁ : ℝ) : ℝ := (a₁ + b₁ * (1 / 2 + N * v)) / 2 + a₁ * (1 / 2 + N * v)

def h2_B2 (v a₁ b₁ : ℝ) : ℝ := (a₁ + b₁ * (1 / 2 + N * v)) / 2 + b₁

theorem h2_measurable_Om {v : ℝ} (hv : 0 < v) (a₁ b₁ R : ℝ) :
    Measurable (Function.uncurry fun x y : Ch N => h2_Om v a₁ b₁ R x y) := by
  unfold h2_Om
  have h1 : Measurable fun p : Ch N × Ch N => ENNReal.ofReal (h2_per (2 * v) (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp ((h2_continuous_per (by positivity : 0 < 2 * v)).measurable.comp
      (measurable_fst.sub measurable_snd))
  have h2 : Measurable fun p : Ch N × Ch N =>
      ENNReal.ofReal (h2_ind R p.1 * (‖h2_perp p.1‖ * (a₁ + b₁ * ‖h2_perp p.2‖))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((h2_measurable_ind R).comp measurable_fst).mul
      ((h2_continuous_perp.norm.measurable.comp measurable_fst).mul
        (measurable_const.add (measurable_const.mul (h2_continuous_perp.norm.measurable.comp measurable_snd))))
  exact h1.mul h2

theorem h2_Om_le_Om0 {v : ℝ} (a₁ b₁ R : ℝ) (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (x y : Ch N) :
    h2_Om v a₁ b₁ R x y ≤ h2_Om v a₁ b₁ 0 x y := by
  unfold h2_Om
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have h0 : h2_ind 0 x = 1 := h2_ind_of_le (norm_nonneg _)
  rw [h0, one_mul]
  have := h2_ind_le_one R x
  have h3 : 0 ≤ ‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖) := by positivity
  nlinarith [h2_ind_nonneg R x]

theorem h2_lintegral_Om_le {v : ℝ} (hv : 0 < v) {a₁ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (R : ℝ)
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    ∫⁻ x in cep_cell N, ∫⁻ y, h2_Om v a₁ b₁ R x y ∂μ ≤
      ENNReal.ofReal (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ∫ y, ‖h2_perp y‖ ^ 2 ∂μ) := by
  have hv2 : 0 < 2 * v := by positivity
  have hW : Measurable (Function.uncurry fun x y : Ch N =>
      ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((h2_measurable_ind R).comp measurable_fst).mul
      ((h2_continuous_perp.norm.measurable.comp measurable_fst).mul
        (measurable_const.add (measurable_const.mul (h2_continuous_perp.norm.measurable.comp measurable_snd))))
  have hper : ∀ x y : Ch N, ENNReal.ofReal (h2_ind R (x + cep_diag N) * (‖h2_perp (x + cep_diag N)‖ *
      (a₁ + b₁ * ‖h2_perp y‖))) = ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖))) := by
    intro x y
    simp only [h2_ind_periodic, h2_perp_periodic]
  have key := h2_lintegral_cell_mu hv2 μ (W := fun x y => ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ *
    (a₁ + b₁ * ‖h2_perp y‖)))) hW hper
  unfold h2_Om
  rw [key]
  set c : ℝ := 1 / 2 + N * v with hc
  have hc0 : 0 ≤ c := by positivity
  have hinner : ∀ y : Ch N, ∫⁻ x, ENNReal.ofReal (h2_g (2 * v) (x - y)) *
      ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖))) ≤
      ENNReal.ofReal (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ‖h2_perp y‖ ^ 2) := by
    intro y
    set r' := ‖h2_perp y‖ with hr'
    have hr'0 : 0 ≤ r' := norm_nonneg _
    have hab : 0 ≤ a₁ + b₁ * r' := by positivity
    calc ∫⁻ x, ENNReal.ofReal (h2_g (2 * v) (x - y)) *
          ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * r')))
        ≤ ∫⁻ x, ENNReal.ofReal (h2_g (2 * v) (x - y)) *
          ENNReal.ofReal ((a₁ + b₁ * r') * (r' + 1 / 2) + (a₁ + b₁ * r') / 2 * ‖x - y‖ ^ 2) := by
          refine lintegral_mono fun x => mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have h1 : ‖h2_perp x‖ ≤ r' + ‖x - y‖ := by
            have : h2_perp x = h2_perp y + h2_perp (x - y) := by rw [← h2_perp_add]; congr 1; abel
            rw [this]
            exact (norm_add_le _ _).trans (add_le_add le_rfl (h2_norm_perp_le _))
          have h2 : ‖x - y‖ ≤ 1 / 2 + ‖x - y‖ ^ 2 / 2 := by nlinarith [sq_nonneg (‖x - y‖ - 1)]
          have h3 := h2_ind_le_one R x
          have h4 := h2_ind_nonneg R x
          have h5 : 0 ≤ ‖h2_perp x‖ * (a₁ + b₁ * r') := by positivity
          calc h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * r')) ≤ 1 * (‖h2_perp x‖ * (a₁ + b₁ * r')) :=
                mul_le_mul_of_nonneg_right h3 h5
            _ ≤ (a₁ + b₁ * r') * (r' + ‖x - y‖) := by nlinarith
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 hab]
      _ = ∫⁻ z, ENNReal.ofReal (h2_g (2 * v) z) *
          ENNReal.ofReal ((a₁ + b₁ * r') * (r' + 1 / 2) + (a₁ + b₁ * r') / 2 * ‖z‖ ^ 2) := by
          rw [← lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (h2_g (2 * v) z) *
            ENNReal.ofReal ((a₁ + b₁ * r') * (r' + 1 / 2) + (a₁ + b₁ * r') / 2 * ‖z‖ ^ 2)) y]
      _ = ENNReal.ofReal ((a₁ + b₁ * r') * (r' + 1 / 2) + (a₁ + b₁ * r') / 2 * (N * (2 * v))) :=
          h2_lintegral_gauss_poly hv2 _ _ (by positivity) (by positivity)
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          unfold h2_A2 h2_B2
          have e : (a₁ + b₁ * r') * (r' + 1 / 2) + (a₁ + b₁ * r') / 2 * (N * (2 * v)) =
              (a₁ + b₁ * r') * (r' + c) := by rw [hc]; ring
          rw [e]
          nlinarith [sq_nonneg (r' - 1), mul_nonneg hb₁ hc0, mul_nonneg ha₁ hc0, mul_nonneg hb₁ (sq_nonneg (r' - 1)),
            mul_nonneg ha₁ (sq_nonneg (r' - 1))]
  calc ∫⁻ y, (∫⁻ x, ENNReal.ofReal (h2_g (2 * v) (x - y)) *
        ENNReal.ofReal (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)))) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ‖h2_perp y‖ ^ 2) ∂μ :=
        lintegral_mono hinner
    _ = _ := by
        have hA2 : 0 ≤ h2_A2 N v a₁ b₁ := by unfold h2_A2; positivity
        have hB2 : 0 ≤ h2_B2 (N := N) v a₁ b₁ := by unfold h2_B2; positivity
        have hi : Integrable (fun y => h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ‖h2_perp y‖ ^ 2) μ :=
          (integrable_const _).add (hmom.const_mul _)
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => by positivity)]
        rw [integral_add (integrable_const _) (hmom.const_mul _), integral_const_mul, integral_const]
        simp

end HRS.MC.CepH2
