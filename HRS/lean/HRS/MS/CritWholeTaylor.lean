import HRS.Whole.Critical
import HRS.Whole.Q34Aux3
import HRS.Equilibrium.L49Aux1
import HRS.MS.CritWholeCap

/-!
# S8.1.K2 -- compensated pole versus the capped quadratic term

Worker S81, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81bd_`.

`s81bd_taylor_cap_error`: for `0 < λ ≤ 1` and a probability density bounded by `M`,
`∫ (taylorH(λ g(x-y)) - λ²/2 · min(g, λ⁻¹)(x-y)²) d(ρ dy) = O(λ²)` with `g = |·|^{-d/2}`,
the constant depending only on `d` and `M`.  The proof dominates the integrand by
`λ g` inside the ball `|z| < λ^{2/d}` and by `λ³ g³` outside it.
(This file imports `HRS.MS.CritWholeCap` only to share the helper `s81bd_sphereArea_pos'`.)
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

theorem s81bd_taylor_cap_error {d : ℕ} (hd : 2 ≤ d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
      IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ x : Euc d,
        Integrable (fun y =>
          taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) -
            (1 / 2 : ℝ) * lam ^ 2 *
              truncKernel d ((d : ℝ) / 2) (lam⁻¹) (x - y) ^ 2)
          (withDensityReal ρ) ∧
        |∫ y, (taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) -
            (1 / 2 : ℝ) * lam ^ 2 *
              truncKernel d ((d : ℝ) / 2) (lam⁻¹) (x - y) ^ 2) ∂(withDensityReal ρ)| ≤
          C * lam ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hA := s81bd_sphereArea_pos' hd1
  refine ⟨max M 0 * (4 * sphereArea d / d), by positivity, ?_⟩
  intro ρ hρ hM lam hlam0 hlam1 x
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by positivity
  have hkern : ∀ z : Euc d, rieszKernel d ((d : ℝ) / 2) z = ‖z‖ ^ (-((d : ℝ) / 2)) :=
    Q34.rieszKernel_eq hs0
  have hk0 : ∀ z : Euc d, 0 ≤ rieszKernel d ((d : ℝ) / 2) z := fun z => by
    rw [hkern]; exact Real.rpow_nonneg (norm_nonneg _) _
  set Dw : Euc d → ℝ := fun w =>
    taylorH (lam * rieszKernel d ((d : ℝ) / 2) w) -
      (1 / 2 : ℝ) * lam ^ 2 * truncKernel d ((d : ℝ) / 2) (lam⁻¹) w ^ 2 with hDw
  have hDmeas : Measurable Dw := by
    have h1 : Measurable (rieszKernel d ((d : ℝ) / 2)) := Q34.measurable_rieszKernel hs0
    have h2 : Measurable (truncKernel d ((d : ℝ) / 2) (lam⁻¹)) := h1.min measurable_const
    exact ((by unfold taylorH; fun_prop : Measurable taylorH).comp (measurable_const.mul h1)).sub
      ((measurable_const.mul (h2.pow_const 2)))
  -- cutoff radius
  set R : ℝ := lam ^ (2 / (d : ℝ)) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hlam0 _
  have hRs : R ^ ((d : ℝ) / 2) = lam := by
    rw [hRdef, ← Real.rpow_mul hlam0.le]
    have : 2 / (d : ℝ) * ((d : ℝ) / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hRs' : R ^ (-((d : ℝ) / 2)) = lam⁻¹ := by
    rw [Real.rpow_neg hRpos.le, hRs]
  -- pointwise domination
  set Hf : Euc d → ℝ≥0∞ := fun w =>
    (Metric.ball (0 : Euc d) R).indicator
      (fun w => ENNReal.ofReal lam * ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) w +
    {w : Euc d | R ≤ ‖w‖}.indicator
      (fun w => ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) w with hHf
  have hpt : ∀ w, ENNReal.ofReal ‖Dw w‖ ≤ Hf w := by
    intro w
    by_cases hw : ‖w‖ < R
    · have hwB : w ∈ Metric.ball (0 : Euc d) R := by simpa using hw
      by_cases hw0 : w = 0
      · subst hw0
        have h00 : (0 : ℝ) ^ (-((d : ℝ) / 2)) = 0 := Real.zero_rpow (neg_ne_zero.2 hs0)
        have : Dw 0 = 0 := by
          simp [hDw, hkern, truncKernel, taylorH, h00, hlam0.le]
        rw [this]
        simp
      · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
        have hge : lam⁻¹ ≤ ‖w‖ ^ (-((d : ℝ) / 2)) := by
          rw [← hRs']
          exact Real.rpow_le_rpow_of_nonpos hwpos hw.le (by linarith)
        have ht1 : 1 ≤ lam * rieszKernel d ((d : ℝ) / 2) w := by
          rw [hkern]
          calc (1 : ℝ) = lam * lam⁻¹ := by field_simp
            _ ≤ lam * ‖w‖ ^ (-((d : ℝ) / 2)) := mul_le_mul_of_nonneg_left hge hlam0.le
        have hmin : truncKernel d ((d : ℝ) / 2) (lam⁻¹) w = lam⁻¹ := by
          simp only [truncKernel, hkern]
          exact min_eq_right hge
        have hDeq : Dw w = taylorH (lam * rieszKernel d ((d : ℝ) / 2) w) - 1 / 2 := by
          simp only [hDw]
          rw [hmin]
          field_simp
        have hb : |Dw w| ≤ lam * ‖w‖ ^ (-((d : ℝ) / 2)) := by
          rw [hDeq, ← hkern, abs_le]
          have h1 := L49.l49_H_nonneg (lam * rieszKernel d ((d : ℝ) / 2) w)
          have h2 := L49.l49_H_le_self (v := lam * rieszKernel d ((d : ℝ) / 2) w)
            (mul_nonneg hlam0.le (hk0 w))
          rw [hkern] at ht1 h1 h2 ⊢
          constructor <;> linarith
        calc ENNReal.ofReal ‖Dw w‖ ≤ ENNReal.ofReal (lam * ‖w‖ ^ (-((d : ℝ) / 2))) := by
              rw [Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal hb
          _ = (Metric.ball (0 : Euc d) R).indicator
                (fun w => ENNReal.ofReal lam * ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) w := by
              rw [Set.indicator_of_mem hwB, ENNReal.ofReal_mul hlam0.le]
          _ ≤ Hf w := by simp only [hHf]; exact le_self_add
    · replace hw := not_lt.1 hw
      have hwpos : 0 < ‖w‖ := hRpos.trans_le hw
      have hwS : w ∈ {w : Euc d | R ≤ ‖w‖} := hw
      have hle : ‖w‖ ^ (-((d : ℝ) / 2)) ≤ lam⁻¹ := by
        rw [← hRs']
        exact Real.rpow_le_rpow_of_nonpos hRpos hw (by linarith)
      have hmin : truncKernel d ((d : ℝ) / 2) (lam⁻¹) w = ‖w‖ ^ (-((d : ℝ) / 2)) := by
        simp only [truncKernel, hkern]
        exact min_eq_left hle
      have hv0 : 0 ≤ lam * ‖w‖ ^ (-((d : ℝ) / 2)) :=
        mul_nonneg hlam0.le (Real.rpow_nonneg (norm_nonneg _) _)
      have hDeq : Dw w = taylorH (lam * ‖w‖ ^ (-((d : ℝ) / 2))) -
          (lam * ‖w‖ ^ (-((d : ℝ) / 2))) ^ 2 / 2 := by
        simp only [hDw]
        rw [hmin, hkern]
        ring
      have hb : |Dw w| ≤ lam ^ 3 * ‖w‖ ^ (-(3 * (d : ℝ) / 2)) := by
        rw [hDeq]
        refine (L49.l49_H_cubic hv0).trans (le_of_eq ?_)
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        push_cast
        ring
      calc ENNReal.ofReal ‖Dw w‖ ≤ ENNReal.ofReal (lam ^ 3 * ‖w‖ ^ (-(3 * (d : ℝ) / 2))) := by
            rw [Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal hb
        _ = {w : Euc d | R ≤ ‖w‖}.indicator
              (fun w => ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) w := by
            rw [Set.indicator_of_mem hwS, ENNReal.ofReal_mul (by positivity)]
        _ ≤ Hf w := by simp only [hHf]; exact le_add_self
  have ma : Measurable (fun w : Euc d => (Metric.ball (0 : Euc d) R).indicator
      (fun w => ENNReal.ofReal lam * ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) w) :=
    (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_norm.pow_const _))).indicator Metric.isOpen_ball.measurableSet
  have mb : Measurable (fun w : Euc d => {w : Euc d | R ≤ ‖w‖}.indicator
      (fun w => ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) w) :=
    (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_norm.pow_const _))).indicator (measurableSet_le measurable_const measurable_norm)
  have hHm : Measurable Hf := ma.add mb
  have hHint : ∫⁻ w, Hf w = ENNReal.ofReal (4 * sphereArea d / d * lam ^ 2) := by
    have hsplit : ∫⁻ w, Hf w = (∫⁻ w, (Metric.ball (0 : Euc d) R).indicator
        (fun w => ENNReal.ofReal lam * ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) w) +
        ∫⁻ w, {w : Euc d | R ≤ ‖w‖}.indicator
        (fun w => ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) w :=
      lintegral_add_left ma _
    have e1 : ∫⁻ w, (Metric.ball (0 : Euc d) R).indicator
        (fun w => ENNReal.ofReal lam * ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) w =
        ENNReal.ofReal (2 * sphereArea d / d * lam ^ 2) := by
      rw [lintegral_indicator Metric.isOpen_ball.measurableSet,
        lintegral_const_mul (f := fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-((d : ℝ) / 2)))) _
          (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)),
        Q34.lintegral_ball_rpow hd1 hRpos (by linarith),
        ← ENNReal.ofReal_mul hlam0.le]
      congr 1
      have : (d : ℝ) - (d : ℝ) / 2 = (d : ℝ) / 2 := by ring
      rw [this, hRs]
      field_simp
    have e2 : ∫⁻ w, {w : Euc d | R ≤ ‖w‖}.indicator
        (fun w => ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) w =
        ENNReal.ofReal (2 * sphereArea d / d * lam ^ 2) := by
      rw [lintegral_indicator (measurableSet_le measurable_const measurable_norm),
        lintegral_const_mul (f := fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-(3 * (d : ℝ) / 2)))) _
          (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)),
        Q34.lintegral_compl_rpow hd1 hRpos (by
          have : (d : ℝ) < 3 * d / 2 := by linarith
          exact this),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : (d : ℝ) - 3 * d / 2 = -((d : ℝ) / 2) := by ring
      have h2 : 3 * (d : ℝ) / 2 - d = (d : ℝ) / 2 := by ring
      rw [this, h2, hRs']
      field_simp
    rw [hsplit, e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hlint : ∫⁻ y, ENNReal.ofReal ‖Dw (x - y)‖ ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (max M 0 * (4 * sphereArea d / d) * lam ^ 2) := by
    calc ∫⁻ y, ENNReal.ofReal ‖Dw (x - y)‖ ∂(withDensityReal ρ)
        ≤ ∫⁻ y, Hf (x - y) ∂(withDensityReal ρ) := lintegral_mono fun y => hpt _
      _ ≤ ENNReal.ofReal M * ∫⁻ w, Hf w := Q34.lintegral_conv_le hρ hM Hf hHm x
      _ = ENNReal.ofReal (M * (4 * sphereArea d / d * lam ^ 2)) := by
          rw [hHint, ← ENNReal.ofReal_mul hM0]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 0 ≤ 4 * sphereArea d / d * lam ^ 2 := by positivity
          calc M * (4 * sphereArea d / d * lam ^ 2) ≤ max M 0 * (4 * sphereArea d / d * lam ^ 2) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) h1
            _ = _ := by ring
  have hmeas : Measurable fun y => Dw (x - y) := hDmeas.comp (measurable_const.sub measurable_id)
  have hCnn : 0 ≤ max M 0 * (4 * sphereArea d / d) * lam ^ 2 := by positivity
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  · rw [← Real.norm_eq_abs]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    exact ENNReal.toReal_le_of_le_ofReal hCnn hlint

end HRS.Whole.BreakdownS81
