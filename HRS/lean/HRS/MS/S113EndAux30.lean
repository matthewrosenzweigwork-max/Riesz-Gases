import HRS.MS.S113EndAux29

/-!
# S11.3 endpoint (worker S11X), part 30: uniform facts for the logarithmic kernel under a Gaussian envelope (S11.6 (a) input)

For a density `ρ ≤ C₁ e^{-a₀|x|²}` of mass one: `g*μ = b_μ - ℓ - ∫ℓ dμ` with `0 ≤ b_μ ≤ 2K`, `0 ≤ ∫ℓ dμ ≤ M₀`, so that `-g*μ ≤ ℓ + M₀`,
`|∬g dμ dμ| ≤ 2K + 2M₀`, rows of `g` are `μ`-integrable and `∫(1+|x|)dμ ≤ Mom`; all constants depend only on `d, C₁, a₀`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ} {C₁ a₀ : ℝ}

/-- The uniform row constant. -/
def s113x_Kq (d : ℕ) (C₁ a₀ : ℝ) : ℝ := (q33b_K d (1 / 2) C₁ a₀).toReal

theorem s113x_Kq_nonneg : 0 ≤ s113x_Kq d C₁ a₀ := ENNReal.toReal_nonneg

theorem s113x_moment_integrable (hC : 0 ≤ C₁) (ha : 0 < a₀) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) (hd : 1 ≤ d) :
    Integrable (fun x : Euc d => 1 + ‖x‖) (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (1 + ‖x‖) ∂(HRS.Whole.withDensityReal ρ) ≤ ∫ x : Euc d, (1 + ‖x‖) * (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) := by
  have hdom : Integrable (fun x : Euc d => (1 + ‖x‖) * (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2))) := by
    have := s113x_poly_gauss_integrable hd ha 1 1
    refine (this.const_mul C₁).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hfm : Measurable (fun x : Euc d => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hm
  have hmeas : AEStronglyMeasurable (fun x : Euc d => ρ x * (1 + ‖x‖)) volume :=
    (hm.mul (measurable_const.add measurable_norm)).aestronglyMeasurable
  have hbd : ∀ x, ρ x * (1 + ‖x‖) ≤ (1 + ‖x‖) * (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) := fun x => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hρ x).2 (by positivity)
  have hint : Integrable (fun x : Euc d => ρ x * (1 + ‖x‖)) volume := by
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ x).1 (by positivity))]
    exact hbd x
  constructor
  · unfold HRS.Whole.withDensityReal
    rw [integrable_withDensity_iff_integrable_smul' hfm (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ x).1]
  · rw [HRS.MP.RdRem.mrr_integral_withDensityReal ρ hm (fun x => (hρ x).1)]
    exact integral_mono hint hdom hbd


theorem s113x_X4_facts (hd : 1 ≤ d) (hC : 0 ≤ C₁) (ha : 0 < a₀) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) (hint : ∫ x, ρ x = 1) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) ∧
      (∀ x, Integrable (fun y => rieszKernel d 0 (x - y)) (HRS.Whole.withDensityReal ρ)) ∧
      Measurable (HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ)) ∧
      (∀ x, -HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) x ≤
        q33b_ell x + 2 * ∫ x : Euc d, q33b_Phi C₁ a₀ x) ∧
      |HRS.Whole.energyPairing (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ)| ≤
        2 * (2 * s113x_Kq d C₁ a₀) + 2 * (2 * ∫ x : Euc d, q33b_Phi C₁ a₀ x) := by
  have hε0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hεd : (1 / 2 : ℝ) < d := by linarith
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := q33b_prob hm (fun x => (hρ x).1) hint
  have hKfin := q33b_K_ne_top hd hεd hC ha
  have hKq0 : 0 ≤ s113x_Kq d C₁ a₀ := s113x_Kq_nonneg
  have hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (1 / 2 * q33b_b x y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (s113x_Kq d C₁ a₀) := fun y => by
    unfold s113x_Kq
    rw [ENNReal.ofReal_toReal hKfin]
    exact q33b_row hd hε0 hε1 hεd hC ha hm hρ y
  have hℓ := q33b_ell_integrable hε0 hε1 hC ha hm hρ
  obtain ⟨hell0, hell1⟩ := s113x_ell_integral_bound hC ha hm hρ
  have hconv := q33b_conv_eq hε0 hKq0 hℓ hrow
  refine ⟨hprob, fun x => ?_, ?_, fun x => ?_, ?_⟩
  · -- rows
    have hb := q33b_b_integrable hε0 hKq0 hrow x
    refine ((hb.sub (integrable_const (q33b_ell x))).sub hℓ).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [q33b_b, Pi.sub_apply]
    ring
  · have : HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) =
        fun x => q33b_bmu (HRS.Whole.withDensityReal ρ) x - q33b_ell x - ∫ z, q33b_ell z ∂(HRS.Whole.withDensityReal ρ) :=
      funext hconv
    rw [this]
    exact ((q33b_bmu_measurable _).sub q33b_ell_measurable).sub measurable_const
  · rw [hconv x]
    have := (q33b_bmu_bounds hε0 hKq0 hrow x).1
    linarith
  · have hG : HRS.Whole.energyPairing (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ) =
        ∫ x, HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) x ∂(HRS.Whole.withDensityReal ρ) := rfl
    rw [hG, q33b_conv_integral hε0 hKq0 hℓ hrow]
    have hbm : 0 ≤ ∫ x, q33b_bmu (HRS.Whole.withDensityReal ρ) x ∂(HRS.Whole.withDensityReal ρ) :=
      integral_nonneg fun x => (q33b_bmu_bounds hε0 hKq0 hrow x).1
    have hbm' : ∫ x, q33b_bmu (HRS.Whole.withDensityReal ρ) x ∂(HRS.Whole.withDensityReal ρ) ≤ 2 * s113x_Kq d C₁ a₀ := by
      have := norm_integral_le_of_norm_le_const (μ := HRS.Whole.withDensityReal ρ)
        (f := fun x => q33b_bmu (HRS.Whole.withDensityReal ρ) x) (C := s113x_Kq d C₁ a₀ / (1 / 2))
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (q33b_bmu_bounds hε0 hKq0 hrow x).1]
          exact (q33b_bmu_bounds hε0 hKq0 hrow x).2)
      simp only [probReal_univ, mul_one] at this
      rw [Real.norm_of_nonneg hbm] at this
      linarith [show s113x_Kq d C₁ a₀ / (1 / 2) = 2 * s113x_Kq d C₁ a₀ by ring]
    rw [abs_le]
    constructor <;> nlinarith

end HRS.MS.S113BD

end
