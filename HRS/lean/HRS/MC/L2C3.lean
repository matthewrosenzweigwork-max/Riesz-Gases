import HRS.MC.L2C3Aux11

/-!
# Packet L2C-3: `L²` exponential stability and comparison of the nonautonomous adjoint

Relocated proof of `HRS.MC.L2Cov.l2cs_adjoint_L2_decay_comparison` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the identification is checked in `HRS/MC/L2C3Tie.lean`).

Route A: the `A_β⁻¹`-Lyapunov functional `Fv(τ) = ⟨y, A_β⁻¹ y⟩_{L²(μ_β)}` of
`y(τ) = P_β U^{t-τ,t}φ - S(τ)` (`S = 0` for (1) and (3), `S` the frozen semigroup for (2)); the perturbation
is controlled by the form bound of L2C-3a (`Aux2`, `Aux4`, `Aux6`), the differential inequality is closed by
AM-GM and the weighted Poincaré inequality (`Aux7`, `Aux9`, `Aux10`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.L2C3

open HRS HRS.Sec7

variable {d : ℕ}

/-- (Packet L2C-3.)  Verbatim copy of `HRS.MC.L2Cov.l2cs_adjoint_L2_decay_comparison`. -/
theorem l2c3_proof (R : Regime d) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t →
        PDE.l2NormSq (projMean (withDensityReal R.ρβ) (propagator R.D R.ρ r t φ)) ≤
          C * Real.exp (-c * (t - r)) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) ∧
        PDE.l2NormSq (fun x => projMean (withDensityReal R.ρβ) (propagator R.D R.ρ r t φ) x -
            PDE.equilibriumSemigroup R.D R.ρβ (t - r) (projMean (withDensityReal R.ρβ) φ) x) ≤
          C * Real.exp (-c * (t - r)) * Real.exp (-κ * r) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) ∧
        ∫ v in Set.Icc r t, ∫ x, ‖Torus.grad (propagator R.D R.ρ v t φ) x‖ ^ 2 ≤
          C * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by
  obtain ⟨Cx⟩ := l2c3_ctx R
  obtain ⟨Cm, κ, hCm, hκ, hL⟩ := l2c3_lyap R Cx
  obtain ⟨K1, K2, hK1, hK2, H1⟩ := l2c3_stage1 R Cx hCm hκ hL
  obtain ⟨K3, hK3, H3⟩ := l2c3_stage3 R Cx hCm hκ hL hK2.le
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have ha := l2c3_rate_pos R Cx
  have hc₀ := Cx.hc₀
  refine ⟨1 + K1 + K3 + Cx.c₀⁻¹ * (K2 / R.β⁻¹), l2c3_rate R Cx / 2, κ, by positivity, by positivity,
    hκ, fun φ hφ r t hr hrt => ?_⟩
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) :=
    integral_nonneg fun x => sq_nonneg _
  set Q := PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) with hQ
  set C : ℝ := 1 + K1 + K3 + Cx.c₀⁻¹ * (K2 / R.β⁻¹) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ Cx.c₀⁻¹ * (K2 / R.β⁻¹) := by positivity
    linarith
  rcases (hr.trans hrt).eq_or_lt with h0 | ht
  · -- degenerate case `t = 0`
    obtain rfl : t = 0 := h0.symm
    obtain rfl : r = 0 := le_antisymm hrt hr
    obtain ⟨z1, z2⟩ := l2c3_zero_case R Cx hφ
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · have h0 : ∫ v in Set.Icc (0 : ℝ) 0, ∫ x, ‖Torus.grad (propagator R.D R.ρ v 0 φ) x‖ ^ 2 = 0 := by
        rw [Set.Icc_self]; simp
      rw [h0]
      exact mul_nonneg (by linarith) hQ0
  · obtain ⟨F, hF, hprop⟩ := l2c3_classical R ht hφ
    have hFs : ∀ s ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F s) := fun s hs => by
      rw [← hprop s hs]; exact (HRS.MC.L2C0.l2c0_proof R φ hφ s t hs.1 hs.2).1
    have hFr : propagator R.D R.ρ r t φ = F r := hprop r ⟨hr, hrt⟩
    have hτ : t - r ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
    have hFt : t - (t - r) = r := by ring
    obtain ⟨h1, h2⟩ := H1 ht hF hFs
    have hE : 0 ≤ Real.exp (-(l2c3_rate R Cx / 2) * (t - r)) := (Real.exp_pos _).le
    have hE' : 0 ≤ Real.exp (-κ * r) := (Real.exp_pos _).le
    refine ⟨?_, ?_, ?_⟩
    · have := h1 (t - r) hτ
      rw [hFt] at this
      rw [hFr]
      refine this.trans ?_
      have hexp : Real.exp (-l2c3_rate R Cx * (t - r)) ≤ Real.exp (-(l2c3_rate R Cx / 2) * (t - r)) :=
        Real.exp_le_exp.2 (by nlinarith [hτ.1])
      have : 0 ≤ (C - K1) * (Real.exp (-(l2c3_rate R Cx / 2) * (t - r)) * Q) :=
        mul_nonneg (by simp only [hC]; have : 0 ≤ Cx.c₀⁻¹ * (K2 / R.β⁻¹) := by positivity
                       linarith) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hexp (mul_nonneg hK1.le hQ0)]
    · have := H3 ht hφ hF hFs (t - r) hτ (h2 (t - r) hτ)
      rw [hFt] at this
      rw [hFr]
      refine this.trans ?_
      have : 0 ≤ (C - K3) * (Real.exp (-κ * r) * Real.exp (-(l2c3_rate R Cx / 2) * (t - r)) * Q) :=
        mul_nonneg (by simp only [hC]; have : 0 ≤ Cx.c₀⁻¹ * (K2 / R.β⁻¹) := by positivity
                       linarith) (by positivity)
      nlinarith
    · have hcongr : ∫ v in Set.Icc r t, ∫ x, ‖Torus.grad (propagator R.D R.ρ v t φ) x‖ ^ 2 =
          ∫ v in Set.Icc r t, ∫ x, ‖Torus.grad (F v) x‖ ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
        simp only [hprop v ⟨hr.trans hv.1, hv.2⟩]
      rw [hcongr, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrt]
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun v => ∫ x, ‖Torus.grad (F v) x‖ ^ 2) (a := 0) (b := t - r) t
      rw [hFt, sub_zero] at hsub
      rw [← hsub]
      have hst := l2c3_stage2 R Cx hF hFs hτ (h2 (t - r) hτ)
      refine hst.trans ?_
      have : Cx.c₀⁻¹ * (K2 * Q / R.β⁻¹) = (Cx.c₀⁻¹ * (K2 / R.β⁻¹)) * Q := by ring
      rw [this]
      have : 0 ≤ (C - Cx.c₀⁻¹ * (K2 / R.β⁻¹)) * Q :=
        mul_nonneg (by simp only [hC]; linarith) hQ0
      nlinarith

end HRS.MC.L2C3
