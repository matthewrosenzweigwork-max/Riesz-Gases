import HRS.MS.ShiftFldAux14

/-!
# S79P: the nonlocal term as a Riesz convolution (a.e.)

`s79g_nl_ae`: for `u ∈ C_b²` with continuous `nlTermRd`, `nlTermRd D ρ u x = ∫ g(x-y) ρ(y) 𝒜u(y) dy` for a.e. `x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21
open HRS (Euc)

variable {d : ℕ}

theorem s79g_Aop_cont_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) :
    Continuous (Aop d s a β (thermalDensity d s a β) u) ∧
      ∃ K : ℝ, ∀ y, |Aop d s a β (thermalDensity d s a β) u y| ≤ K * (1 + ‖y‖) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hU2 : ContDiff ℝ 2 (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) := by
    exact_mod_cast contDiff_infty.1 hT.Usmooth 2
  have hbc : Continuous (bdr d s a β (thermalDensity d s a β)) := by
    have : bdr d s a β (thermalDensity d s a β) = fun x =>
        -(a • x + gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) :=
      funext fun x => s79g_drift hd hs0 hsd ha hβ hρ x
    rw [this]
    exact ((continuous_id.const_smul a).add (S45.s45_contDiff_gradient hU2).continuous).neg
  have hgc : Continuous (gradient u) := (S45.s45_contDiff_gradient hu.1).continuous
  refine ⟨?_, ?_⟩
  · unfold Aop
    exact (s21_lap_continuous hu.1).neg.sub (continuous_const.mul (hbc.inner hgc))
  · refine ⟨d * HRS.cbNorm 2 u + β * (a + BU) * HRS.cbNorm 2 u, fun y => ?_⟩
    have hb : ‖bdr d s a β (thermalDensity d s a β) y‖ ≤ a * ‖y‖ + BU := by
      rw [s79g_drift hd hs0 hsd ha hβ hρ y, norm_neg]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      exact add_le_add le_rfl (hT.gradU_le y)
    have hg := s21_grad_bound hu y
    have hl := s21_lap_bound hu y
    have hc0 : 0 ≤ HRS.cbNorm 2 u := (norm_nonneg _).trans hg
    have hin : |inner ℝ (bdr d s a β (thermalDensity d s a β) y) (gradient u y)| ≤
        (a * ‖y‖ + BU) * HRS.cbNorm 2 u :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hb hg (norm_nonneg _)
        ((norm_nonneg _).trans hb))
    unfold Aop
    have hBU : 0 ≤ BU := hT.BU0
    have hn := norm_nonneg y
    calc |-(Laplacian.laplacian u y) - β * inner ℝ (bdr d s a β (thermalDensity d s a β) y) (gradient u y)|
        ≤ |Laplacian.laplacian u y| + β * |inner ℝ (bdr d s a β (thermalDensity d s a β) y) (gradient u y)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg, abs_mul, abs_of_pos hβ]
      _ ≤ d * HRS.cbNorm 2 u + β * ((a * ‖y‖ + BU) * HRS.cbNorm 2 u) :=
          add_le_add hl (mul_le_mul_of_nonneg_left hin hβ.le)
      _ ≤ _ := by nlinarith [mul_nonneg hβ.le (mul_nonneg ha.le hc0), mul_nonneg hβ.le (mul_nonneg hBU hc0),
            mul_nonneg hn (mul_nonneg hβ.le (mul_nonneg ha.le hc0)), mul_nonneg hn hc0,
            mul_nonneg hn (mul_nonneg hβ.le (mul_nonneg hBU hc0))]

theorem s79g_h_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) :
    Continuous (fun y => thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y) ∧
    Integrable (fun y => (1 + ‖y‖) *
      |thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y|) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨hAc, K, hK⟩ := s79g_Aop_cont_bound hd hs0 hsd ha hβ hρ hu
  refine ⟨hT.smooth.continuous.mul hAc, ?_⟩
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (c := c / 2) (by have := hT.hc; positivity)
  have hint := s79g_gdom (C := C * Cp) (c := c / 2) (by have := hT.hc; positivity)
    (mul_nonneg hT.C0 hCp0)
    (a := fun y : Euc d => (1 + ‖y‖) * thermalDensity d s a β y) (f := fun y => |Aop d s a β (thermalDensity d s a β) u y|)
    ((continuous_const.add continuous_norm).mul hT.smooth.continuous).aestronglyMeasurable
    hAc.abs.aestronglyMeasurable
    (fun y => by
      have hn := norm_nonneg y
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖y‖), abs_of_nonneg (hT.prob.nonneg y)]
      have h1 : thermalDensity d s a β y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (le_abs_self _).trans (hT.h0 y)
      have h2 := hCp ‖y‖ hn
      have e : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) = Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (1 + ‖y‖) * thermalDensity d s a β y ≤ (Cp * Real.exp (c / 2 * ‖y‖ ^ 2)) *
            (C * Real.exp (-c * ‖y‖ ^ 2)) :=
            mul_le_mul h2 h1 (hT.prob.nonneg y) (by positivity)
        _ = C * Cp * (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by rw [e])
    (K := K) (fun y => by simpa using hK y)
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [abs_mul, abs_of_nonneg (hT.prob.nonneg y)]
  ring

end HRS.MS.S79G
