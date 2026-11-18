import HRS.Sections.QuenchAux14

/-!
# Packet QUENCH (Q27), part 15: Doob bound for the OU noise

Pathwise: `G = σB - λ∫G` implies `sup_{t≤T}|G| ≤ 2σ sup_{t≤T}|B|` (integrating factor).  Then Doob's `L²`
inequality for the Brownian motion `B` (Brownian filtration from `exists_isBrownianFiltration`) gives
`E sup_{t≤T}|G|² ≤ 16 σ² T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

/-- Deterministic bound: if `g + λ∫_0^s g` is bounded by `σM` on `[0,T]`, then `|g| ≤ 2σM` there. -/
theorem ode_bound {g : ℝ → ℝ} (hg : Continuous g) {lam σ M T : ℝ} (hlam : 0 < lam) (hσ : 0 ≤ σ)
    (hM : 0 ≤ M) (hB : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s + lam * ∫ u in (0 : ℝ)..s, g u| ≤ σ * M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, |g t| ≤ 2 * σ * M := by
  intro t ht
  set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, g u with hF
  have hFd : ∀ s, HasDerivAt F (g s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  -- `u(s) = e^{λ s} F(s)`
  have hud : ∀ s, HasDerivAt (fun s => Real.exp (lam * s) * F s)
      (Real.exp (lam * s) * (g s + lam * F s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s := by
      simpa using ((hasDerivAt_id s).const_mul lam).exp
    have := h1.mul (hFd s)
    convert this using 1
    ring
  have hcont : Continuous fun s => Real.exp (lam * s) * (g s + lam * F s) := by
    have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hFd s).continuousAt
    fun_prop
  have hFt : ∀ s ∈ Set.Icc (0 : ℝ) T, |F s| ≤ σ * M / lam := by
    intro s hs
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hud x)
      (hcont.intervalIntegrable 0 s)
    simp only [hF, intervalIntegral.integral_same, mul_zero, Real.exp_zero, one_mul, sub_zero] at hint
    have hs0 := hs.1
    have hbound : |∫ x in (0 : ℝ)..s, Real.exp (lam * x) * (g x + lam * ∫ u in (0 : ℝ)..x, g u)| ≤
        ∫ x in (0 : ℝ)..s, Real.exp (lam * x) * (σ * M) := by
      refine (intervalIntegral.abs_integral_le_integral_abs hs0).trans ?_
      refine intervalIntegral.integral_mono_on hs0 ?_ ?_ ?_
      · exact (hcont.abs).intervalIntegrable 0 s
      · exact (Continuous.intervalIntegrable (by fun_prop) 0 s)
      · intro x hx
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hB x ⟨hx.1, hx.2.trans hs.2⟩) (Real.exp_pos _).le
    have hexp : ∫ x in (0 : ℝ)..s, Real.exp (lam * x) * (σ * M) = σ * M * ((Real.exp (lam * s) - 1) / lam) := by
      have hd' : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun x => σ * M / lam * Real.exp (lam * x))
          (Real.exp (lam * x) * (σ * M)) x := by
        intro x _
        have := (((hasDerivAt_id' x).const_mul lam).exp).const_mul (σ * M / lam)
        convert this using 1
        field_simp [hlam.ne']
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd' (Continuous.intervalIntegrable (by fun_prop) _ _)]
      simp only [mul_zero, Real.exp_zero]
      field_simp [hlam.ne']
    rw [hint] at hbound
    rw [hexp] at hbound
    have h2 : |Real.exp (lam * s) * F s| = Real.exp (lam * s) * |F s| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [h2] at hbound
    have h3 : Real.exp (lam * s) * |F s| ≤ σ * M * ((Real.exp (lam * s) - 1) / lam) := hbound
    have h4 : 0 < Real.exp (lam * s) := Real.exp_pos _
    have h5 : |F s| ≤ σ * M * ((Real.exp (lam * s) - 1) / lam) / Real.exp (lam * s) :=
      (le_div_iff₀ h4).2 (by linarith)
    refine h5.trans ?_
    rw [div_le_iff₀ h4]
    have : σ * M * ((Real.exp (lam * s) - 1) / lam) ≤ σ * M / lam * Real.exp (lam * s) := by
      rw [mul_div_assoc']
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hlam.le
      nlinarith [mul_nonneg hσ hM, h4]
    exact this
  have h1 := hB t ht
  have h2 := hFt t ht
  have hgt : g t = (g t + lam * F t) - lam * F t := by ring
  rw [hgt]
  refine (abs_sub _ _).trans ?_
  have : lam * |F t| ≤ σ * M := by
    calc lam * |F t| ≤ lam * (σ * M / lam) := mul_le_mul_of_nonneg_left h2 hlam.le
      _ = σ * M := by field_simp
  rw [abs_mul, abs_of_pos hlam] at *
  linarith

end Qch

end HRS
