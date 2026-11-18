import HRS.MS.S81G_Sing
import HRS.Energy.PressureDV

/-!
# S81G, packet G3b: finite relative entropy against a Gibbs law gives a finite second moment

`s81g_second_moment`: if `H(η | sb1Gam D k N) < ∞` then `∫ ‖x‖² dη < ∞` (Donsker-Varadhan `dv_lintegral` with
`F = c‖x‖²`, `c` below the Gaussian rate of the Boltzmann weight).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.MS.MfeConf HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S81G

variable {d N : ℕ} {D : Whole.WholeDyn d} {k : Euc d → ℝ}

theorem s81g_exp_moment (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    ∃ c : ℝ, 0 < c ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂(sb1Gam D k N) < ⊤ := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hθ
  have hz := s81g_gz_pos hθ hHm hlow hcV hV
  set a1 : ℝ := D.invβ⁻¹ * cV / 2 with ha1
  have ha10 : 0 < a1 := by positivity
  set c : ℝ := a1 / 2 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, ?_⟩
  set C0 : ℝ := Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) / sb1Gz D k N with hC0
  have hC00 : 0 ≤ C0 := by positivity
  have hqm : Measurable (sb1Gq D k N) := (s81g_Gw_meas hHm).div_const _
  unfold sb1Gam sb1Dm
  have hgm : Measurable (fun x : Whole.EucConfig d N => ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2))) :=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2))).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul₀ hqm.ennreal_ofReal.aemeasurable hgm.aemeasurable]
  have hint : Integrable (fun Ξ : Whole.EucConfig d N => C0 * Real.exp (-(c * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := c) hc0).const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
  have hq0 : 0 ≤ sb1Gq D k N x := (div_pos (Real.exp_pos _) hz).le
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hqle : sb1Gq D k N x ≤ C0 * Real.exp (-(a1 * ‖x‖ ^ 2)) := by
    unfold sb1Gq
    rw [hC0, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (sb1_Gw_le hθ hlow hcV hV x) hz.le
  have e : Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(a1 * ‖x‖ ^ 2)) = Real.exp (-(c * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; rw [hc]; ring
  calc sb1Gq D k N x * Real.exp (c * ‖x‖ ^ 2) = Real.exp (c * ‖x‖ ^ 2) * sb1Gq D k N x := mul_comm _ _
    _ ≤ Real.exp (c * ‖x‖ ^ 2) * (C0 * Real.exp (-(a1 * ‖x‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hqle (Real.exp_pos _).le
    _ = C0 * (Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(a1 * ‖x‖ ^ 2))) := by ring
    _ = C0 * Real.exp (-(c * ‖x‖ ^ 2)) := by rw [e]

theorem s81g_second_moment (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    (η : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure η]
    (hKL : klDiv η (sb1Gam D k N) ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂η < ⊤ := by
  haveI := s81g_gam_prob hθ hHm hlow hcV hV
  obtain ⟨c, hc0, hL⟩ := s81g_exp_moment hθ hHm hlow hcV hV
  set L : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (c * ‖x‖ ^ 2)) ∂(sb1Gam D k N) with hLdef
  have hK0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  have hLle : L ≤ ENNReal.ofReal (Real.exp L.toReal) := by
    calc L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hL.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp L.toReal])
  have hdv := dv_lintegral (sb1Gam D k N) η hKL (F := fun x => c * ‖x‖ ^ 2)
    (measurable_const.mul (measurable_norm.pow_const 2)) (fun x => by positivity) hK0 hLle
  have hfin : ∫⁻ x, ENNReal.ofReal (c * ‖x‖ ^ 2) ∂η < ⊤ :=
    lt_of_le_of_lt hdv (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hKL, ENNReal.ofReal_lt_top⟩)
  have e : ∀ x : Whole.EucConfig d N, ENNReal.ofReal (‖x‖ ^ 2) =
      ENNReal.ofReal (c⁻¹) * ENNReal.ofReal (c * ‖x‖ ^ 2) := fun x => by
    rw [← ENNReal.ofReal_mul (inv_pos.2 hc0).le]
    congr 1
    field_simp
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end HRS.MS.S81G
