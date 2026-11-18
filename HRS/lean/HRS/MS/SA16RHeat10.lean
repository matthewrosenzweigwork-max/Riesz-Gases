import HRS.MS.SA16RHeat9

/-!
# S.A.16 (SA16R) Heat10: the approximate identity

`sa16r_approx_id`: for `u ∈ C_c^∞` and `p ≥ 1`, `‖g_a ⋆ u - u‖_p → 0` as `a → 0+`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat10
variable {d : ℕ}

lemma sa16r_lint_g_one {a : ℝ} (ha : 0 < a) : ∫⁻ z, ‖sa16r_g d a z‖ₑ = 1 := by
  have : ∫⁻ z, ‖sa16r_g d a z‖ₑ = ENNReal.ofReal (∫ z, sa16r_g d a z) := by
    rw [ofReal_integral_eq_lintegral_ofReal (sa16r_g_int ha)
      (Eventually.of_forall fun z => (sa16r_g_pos ha z).le)]
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal (sa16r_g_pos ha z).le]
  rw [this, sa16r_g_mass ha]; simp

lemma sa16r_cv_sub_self {a : ℝ} (ha : 0 < a) {u : Euc d → ℝ} (hu : IsCcInfty u) (x : Euc d) :
    sa16r_cv (sa16r_g d a) u x - u x = ∫ z, sa16r_g d a z * (u (x - z) - u x) := by
  have h1 := sa16r_cv_integrand (sa16r_g_int ha) hu x
  have h2 : Integrable (fun z => sa16r_g d a z * u x) := (sa16r_g_int ha).mul_const _
  have : ∫ z, sa16r_g d a z * (u (x - z) - u x) =
      (∫ z, sa16r_g d a z * u (x - z)) - ∫ z, sa16r_g d a z * u x := by
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [mul_sub]
  rw [this, integral_mul_const, sa16r_g_mass ha, one_mul]
  rfl

lemma sa16r_approx_lint_le {a : ℝ} (ha : 0 < a) {u : Euc d → ℝ} (hu : IsCcInfty u) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖sa16r_cv (sa16r_g d a) u x - u x‖ₑ ^ p ≤
      ∫⁻ z, ‖sa16r_g d a z‖ₑ * sa16r_T u p z := by
  have hp0 : 0 ≤ p := by linarith
  have hpt : ∀ x, ‖sa16r_cv (sa16r_g d a) u x - u x‖ₑ ^ p ≤
      (∫⁻ z, ‖sa16r_g d a z‖ₑ * ‖u (x - z) - u x‖ₑ) ^ p := by
    intro x
    refine ENNReal.rpow_le_rpow ?_ hp0
    rw [sa16r_cv_sub_self ha hu x]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [enorm_mul]
  have hF : Measurable (Function.uncurry fun (x z : Euc d) => ‖u (x - z) - u x‖ₑ) :=
    ((hu.1.continuous.comp (continuous_fst.sub continuous_snd)).sub
      (hu.1.continuous.comp continuous_fst)).measurable.enorm
  have hm := sa16j_mink (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d))) hp
    (a := fun z => ‖sa16r_g d a z‖ₑ) sa16r_g_meas.enorm hF
  rw [sa16r_lint_g_one ha, ENNReal.one_rpow, one_mul] at hm
  calc ∫⁻ x, ‖sa16r_cv (sa16r_g d a) u x - u x‖ₑ ^ p
      ≤ ∫⁻ x, (∫⁻ z, ‖sa16r_g d a z‖ₑ * ‖u (x - z) - u x‖ₑ) ^ p := lintegral_mono hpt
    _ ≤ ∫⁻ z, ‖sa16r_g d a z‖ₑ * ∫⁻ x, ‖u (x - z) - u x‖ₑ ^ p := hm
    _ = _ := rfl

lemma sa16r_tail_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun a : ℝ => ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a)))))
      (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => δ ^ 2 / (8 * a)) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (by positivity : 0 < δ ^ 2 / 8)
    refine this.congr fun a => ?_
    field_simp
  have h2 : Tendsto (fun a : ℝ => Real.exp (-(δ ^ 2 / (8 * a)))) (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  have h3 := (h2.const_mul ((2 : ℝ) ^ ((d : ℝ) / 2)))
  rw [mul_zero] at h3
  have := ENNReal.tendsto_ofReal h3
  simpa using this

lemma sa16r_approx_lint_tendsto {u : Euc d → ℝ} (hu : IsCcInfty u) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun a : ℝ => ∫⁻ x, ‖sa16r_cv (sa16r_g d a) u x - u x‖ₑ ^ p) (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun a => by rw [hεtop]; exact le_top
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hTt := (ENNReal.tendsto_nhds_zero.1 (sa16r_T_tendsto hu.1.continuous hu.2 hp0)) (ε / 2) hε2
  obtain ⟨δ, hδ, hδT⟩ := Metric.eventually_nhds_iff.1 hTt
  set C : ℝ≥0∞ := 2 ^ p * ∫⁻ x, ‖u x‖ₑ ^ p with hC
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (by norm_num))
    (sa16r_lint_u_lt hu.1.continuous hu.2 hp0).ne
  have htail := sa16r_tail_tendsto (d := d) hδ
  have hC0 : Tendsto (fun a : ℝ => C * ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (-(δ ^ 2 / (8 * a))))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul htail (Or.inr hCtop)
    simpa using this
  have hev := (ENNReal.tendsto_nhds_zero.1 hC0) (ε / 2) hε2
  filter_upwards [hev, self_mem_nhdsWithin] with a hεa ha
  have ha' : 0 < a := ha
  refine (sa16r_approx_lint_le ha' hu hp).trans ?_
  have hpt : ∀ z : Euc d, ‖sa16r_g d a z‖ₑ * sa16r_T u p z ≤
      ‖sa16r_g d a z‖ₑ * (ε / 2) +
        {z : Euc d | δ ≤ ‖z‖}.indicator (fun z => ‖sa16r_g d a z‖ₑ * C) z := by
    intro z
    by_cases hz : δ ≤ ‖z‖
    · rw [indicator_of_mem (show z ∈ {z : Euc d | δ ≤ ‖z‖} from hz)]
      exact (mul_le_mul' (le_refl _) (sa16r_T_le hu.1.continuous hp z)).trans le_add_self
    · rw [indicator_of_notMem (show z ∉ {z : Euc d | δ ≤ ‖z‖} from hz), add_zero]
      exact mul_le_mul' (le_refl _) (hδT (by simpa [dist_zero_right] using not_le.1 hz))
  calc ∫⁻ z, ‖sa16r_g d a z‖ₑ * sa16r_T u p z
      ≤ ∫⁻ z, (‖sa16r_g d a z‖ₑ * (ε / 2) +
        {z : Euc d | δ ≤ ‖z‖}.indicator (fun z => ‖sa16r_g d a z‖ₑ * C) z) := lintegral_mono hpt
    _ = (∫⁻ z, ‖sa16r_g d a z‖ₑ * (ε / 2)) +
        ∫⁻ z in {z : Euc d | δ ≤ ‖z‖}, ‖sa16r_g d a z‖ₑ * C := by
        rw [lintegral_add_left, lintegral_indicator (measurableSet_le measurable_const measurable_norm)]
        exact sa16r_g_meas.enorm.mul_const _
    _ ≤ ε / 2 + C * ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / (8 * a)))) := by
        gcongr
        · rw [lintegral_mul_const _ sa16r_g_meas.enorm, sa16r_lint_g_one ha', one_mul]
        · rw [lintegral_mul_const _ sa16r_g_meas.enorm, mul_comm]
          exact mul_le_mul' (le_refl _) (sa16r_g_tail ha' hδ.le)
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

end Heat10

end HRS.Whole.AppendixA.Phase2SA16R
