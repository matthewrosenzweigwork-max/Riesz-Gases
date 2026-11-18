import HRS.MS.ToriConvAux5

/-!
# MS-TORI-DRIFTCONV, helper file 6: `Z_L → 1`, `μ_L = c ρ` near `0`, and the level hypothesis for `(μ_L, ρ^t)`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- `|Z_L - 1| ≤ B ε` for `L ≥ 4N`, from the tail of the weight. -/
theorem tcv_Z_close {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) (B : ℝ) (hB0 : 0 ≤ B) (hρB : ∀ y, |ρ y| ≤ B * tca_g y)
    (L : ℝ) (hL : 0 < L) (N : ℕ) (hLN : (N : ℝ) ≤ L / 4) (ε : ℝ)
    (hN : ∫ y in {y : Euc d | (N : ℝ) ≤ ‖y‖}, tca_g y ≤ ε) :
    |(∫ y, ζ (L⁻¹ • y) * ρ y) - 1| ≤ B * ε := by
  have hAm : MeasurableSet {y : Euc d | L / 4 ≤ ‖y‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hρint : Integrable ρ := by
    by_contra h
    have h1 := hρ.integral_one
    rw [integral_undef h] at h1
    norm_num at h1
  have hcont : Continuous (fun y : Euc d => ζ (L⁻¹ • y)) :=
    hζ.1.continuous.comp (continuous_const_smul _)
  have hint1 : Integrable (fun y : Euc d => ζ (L⁻¹ • y) * ρ y) := by
    refine Integrable.mono' hρint.norm
      (hcont.aestronglyMeasurable.mul hρ.measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have hz := hζ.2.2.2.1 (L⁻¹ • y)
    have h1 : ‖ζ (L⁻¹ • y)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]; exact hz.2
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hbound : ∀ y : Euc d, ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ ≤
      {y : Euc d | L / 4 ≤ ‖y‖}.indicator (fun y => B * tca_g y) y := by
    intro y
    by_cases hy : L / 4 ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : Euc d | L / 4 ≤ ‖y‖} from hy)]
      have hz01 := hζ.2.2.2.1 (L⁻¹ • y)
      have h1 : ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ = |ζ (L⁻¹ • y) - 1| * |ρ y| := by
        rw [Real.norm_eq_abs, ← abs_mul]
        congr 1
        ring
      have h2 : |ζ (L⁻¹ • y) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hz01.1, hz01.2]
      calc ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ = |ζ (L⁻¹ • y) - 1| * |ρ y| := h1
        _ ≤ 1 * |ρ y| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = |ρ y| := one_mul _
        _ ≤ B * tca_g y := hρB y
    · rw [Set.indicator_of_notMem (show y ∉ {y : Euc d | L / 4 ≤ ‖y‖} from hy)]
      have hy' : ‖y‖ < L / 4 := lt_of_not_ge hy
      have hz1 : ζ (L⁻¹ • y) = 1 := by
        apply hζ.2.2.2.2
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hL), inv_mul_eq_div, div_le_iff₀ hL]
        linarith
      rw [hz1, one_mul, sub_self, norm_zero]
  have hint_ind : Integrable ({y : Euc d | L / 4 ≤ ‖y‖}.indicator (fun y => B * tca_g y)) :=
    (tca_g_integrable.const_mul B).indicator hAm
  have hdiff : (∫ y, ζ (L⁻¹ • y) * ρ y) - 1 = ∫ y, (ζ (L⁻¹ • y) * ρ y - ρ y) := by
    rw [integral_sub hint1 hρint, hρ.integral_one]
  have hb := norm_integral_le_of_norm_le hint_ind (Filter.Eventually.of_forall hbound)
  rw [integral_indicator hAm, integral_const_mul] at hb
  have hmono : ∫ y in {y : Euc d | L / 4 ≤ ‖y‖}, tca_g y ≤ ε := by
    refine le_trans ?_ hN
    refine setIntegral_mono_set tca_g_integrable.integrableOn
      (Filter.Eventually.of_forall fun y => tca_g_nonneg y) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    intro hy
    show (N : ℝ) ≤ ‖y‖
    exact le_trans hLN hy
  have hmain : ‖∫ y, (ζ (L⁻¹ • y) * ρ y - ρ y)‖ ≤ B * ε :=
    hb.trans (mul_le_mul_of_nonneg_left hmono hB0)
  rw [← hdiff, Real.norm_eq_abs] at hmain
  exact hmain

theorem tcv_inv_sub {Z : ℝ} (hZ : 1 / 2 ≤ Z) : |Z⁻¹ - 1| ≤ 2 * |Z - 1| := by
  have hZ0 : 0 < Z := by linarith
  have e : Z⁻¹ - 1 = (1 - Z) * Z⁻¹ := by field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hZ0), abs_sub_comm]
  have h1 : Z⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hZ0 (by norm_num)]
    linarith
  nlinarith [abs_nonneg (Z - 1)]

theorem tcv_mu_near {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    (n : ℕ) (ρ : Euc d → ℝ) (hρ : ContDiff ℝ (n : WithTop ℕ∞) ρ) (c : ℝ) (y : Euc d)
    (hy : ‖y‖ < L / 4) :
    iteratedFDeriv ℝ n (perL L (fun x => c * (ζ (L⁻¹ • x) * ρ x))) y =
      c • iteratedFDeriv ℝ n ρ y := by
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → c * (ζ (L⁻¹ • y) * ρ y) = 0 := by
    intro y hy
    rw [tca_zeta_far_val hζ L hL y hy, zero_mul, mul_zero]
  rw [tca_perL_central L hL _ hvan y (by linarith) n]
  have hmem : Metric.ball (0 : Euc d) (L / 4) ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
  have heq : (fun x => c * (ζ (L⁻¹ • x) * ρ x)) =ᶠ[𝓝 y] c • ρ := by
    filter_upwards [hmem] with x hx
    have hx' : ‖x‖ < L / 4 := by rwa [Metric.mem_ball, dist_zero_right] at hx
    have hz1 : ζ (L⁻¹ • x) = 1 := by
      apply hζ.2.2.2.2
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hL), inv_mul_eq_div, div_le_iff₀ hL]
      linarith
    simp [hz1]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq n).eq_of_nhds,
    iteratedFDeriv_const_smul_apply hρ.contDiffAt]

theorem tcv_tail_mono {N : ℕ} {r : ℝ} (hr : (N : ℝ) ≤ r) :
    ∫ u in {u : Euc d | r ≤ ‖u‖}, tca_g u ≤ ∫ u in {u : Euc d | (N : ℝ) ≤ ‖u‖}, tca_g u := by
  refine setIntegral_mono_set tca_g_integrable.integrableOn
    (Filter.Eventually.of_forall fun y => tca_g_nonneg y) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  intro hy
  show (N : ℝ) ≤ ‖y‖
  exact le_trans hr hy

end HRS.MS.ToriConv
