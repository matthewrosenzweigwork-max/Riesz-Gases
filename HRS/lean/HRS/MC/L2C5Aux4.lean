import HRS.MC.L2C5Aux3

/-!
# Packet L2C-5, helper 4: the exponentially weighted gradient energy

From the weighted energy estimate of L2C-3 (stage 1, `∫_0^t e^{aσ/2} E_1 ≲ ‖Qφ‖²`, where `σ = t - v` is the time
to the horizon) we get
`∫_0^t e^{-2m(t-σ)} ∫|∇F(t-σ)|² dσ ≤ c₀⁻¹ e^{-μt} B/ν`, `μ = min(2m, a/2)`:
the energy near `v = 0` is damped twice, by the weight `e^{-2mv}` and by the decay of the adjoint.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.MC.L2C3

namespace HRS.MC.L2C5

variable {d : ℕ}

theorem l2c5_exp_ineq {a m σ t : ℝ} (hσ : 0 ≤ σ) (hσt : σ ≤ t) :
    Real.exp (-2 * m * (t - σ)) ≤
      Real.exp (-(min (2 * m) (a / 2)) * t) * Real.exp (a / 2 * σ) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  rcases le_total (2 * m) (a / 2) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.2 h) hσ]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hσt)]

theorem l2c5_weighted_energy (R : Regime d) (Cx : Ctx R) {t : ℝ} (ht : 0 < t) {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution R.D R.ρ t φ F)
    (hFs : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) {m B : ℝ}
    (hW : R.β⁻¹ * ∫ σ in (0 : ℝ)..t, Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ ≤ B) :
    ∫ σ in (0 : ℝ)..t, Real.exp (-2 * m * (t - σ)) * l2c3_Nn R t F σ ≤
      Cx.c₀⁻¹ * (Real.exp (-(min (2 * m) (l2c3_rate R Cx / 2)) * t) * (B / R.β⁻¹)) := by
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have hc₀ := Cx.hc₀
  set a := l2c3_rate R Cx with ha
  set μ := min (2 * m) (a / 2) with hμ
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) t := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hNc : ContinuousOn (l2c3_Nn R t F) (Set.Icc 0 t) := l2c3_Nn_cont hF
  have hEc : ContinuousOn (l2c3_E1 R t F) (Set.Icc 0 t) := l2c3_E1_cont R Cx hF
  have hexpc : Continuous fun σ : ℝ => Real.exp (-2 * m * (t - σ)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hexpc2 : Continuous fun σ : ℝ => Real.exp (a / 2 * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hle : ∫ σ in (0 : ℝ)..t, Real.exp (-2 * m * (t - σ)) * l2c3_Nn R t F σ ≤
      ∫ σ in (0 : ℝ)..t, Cx.c₀⁻¹ * (Real.exp (-μ * t) * (Real.exp (a / 2 * σ) * l2c3_E1 R t F σ)) := by
    refine intervalIntegral.integral_mono_on ht.le
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
          exact (hexpc.continuousOn.mul hNc).integrableOn_Icc)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
          exact (continuousOn_const.mul (continuousOn_const.mul
            (hexpc2.continuousOn.mul hEc))).integrableOn_Icc) fun σ hσ => ?_
    have hσt : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1, hσ.2⟩
    have hF1 : Torus.IsCk 1 (F (t - σ)) := l2c3_isCk_of_smooth (hFs _ (hmem σ hσt)) 1
    have hN := l2c3_Nn_le R Cx hF1
    have hE := l2c3_E1_nonneg R Cx t F σ
    have hN' : l2c3_Nn R t F σ ≤ Cx.c₀⁻¹ * l2c3_E1 R t F σ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hc₀]; linarith
    have hex := l2c5_exp_ineq (a := a) (m := m) hσ.1 hσ.2
    have h1 : 0 ≤ Real.exp (-2 * m * (t - σ)) := (Real.exp_pos _).le
    have h2 : 0 ≤ Cx.c₀⁻¹ * l2c3_E1 R t F σ := mul_nonneg (inv_nonneg.2 hc₀.le) hE
    calc Real.exp (-2 * m * (t - σ)) * l2c3_Nn R t F σ
        ≤ Real.exp (-2 * m * (t - σ)) * (Cx.c₀⁻¹ * l2c3_E1 R t F σ) :=
          mul_le_mul_of_nonneg_left hN' h1
      _ ≤ (Real.exp (-μ * t) * Real.exp (a / 2 * σ)) * (Cx.c₀⁻¹ * l2c3_E1 R t F σ) :=
          mul_le_mul_of_nonneg_right hex h2
      _ = _ := by ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc₀.le))
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [le_div_iff₀ hν]; linarith

end HRS.MC.L2C5
