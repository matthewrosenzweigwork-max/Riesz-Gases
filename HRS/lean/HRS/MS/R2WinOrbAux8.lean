import HRS.MS.R2WinOrbAux7

/-!
# S10.3 (stationary half), part 8: integration by parts for the cosine coefficients and one-sided derivatives of `C^j` jets

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.

* `s103_ibp`: for a Banach-valued `Ψ` on `[0,T]` with `Ψ' = Ψ1`, `Ψ1' = Ψ2` (derivatives within `[0,T]`, bounded) and `sin(λT) = 0`:
  `‖∫_0^T cos(λu) Ψ(u) du‖ ≤ (2A₁ + T A₂)/λ²` (two integrations by parts, boundary terms at `0` and `T`).
* `s103_hasDeriv_iter`: convergence of the difference quotients in the `C^j` sup norm gives a derivative of `τ ↦ D^jF(τ)(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

theorem s103_ibp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hsin : Real.sin (lam * T) = 0)
    {Ψ Ψ1 Ψ2 : ℝ → E}
    (h0 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt Ψ (Ψ1 u) (Set.Icc 0 T) u)
    (h1 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt Ψ1 (Ψ2 u) (Set.Icc 0 T) u)
    {A1 A2 : ℝ} (hA1 : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖Ψ1 u‖ ≤ A1) (hA2 : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖Ψ2 u‖ ≤ A2) :
    ‖∫ u in (0 : ℝ)..T, Real.cos (lam * u) • Ψ u‖ ≤ (2 * A1 + T * A2) / lam ^ 2 := by
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hΨc : ContinuousOn Ψ (Icc 0 T) := fun u hu => (h0 u hu).continuousWithinAt
  have hΨ1c : ContinuousOn Ψ1 (Icc 0 T) := fun u hu => (h1 u hu).continuousWithinAt
  set Φ : ℝ → E := fun u => (Real.sin (lam * u) / lam) • Ψ u + (Real.cos (lam * u) / lam ^ 2) • Ψ1 u with hΦ
  set Φ' : ℝ → E := fun u => Real.cos (lam * u) • Ψ u + (Real.cos (lam * u) / lam ^ 2) • Ψ2 u with hΦ'
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hcontΦ : ContinuousOn Φ (Icc 0 T) := by
    refine ContinuousOn.add (ContinuousOn.smul (by fun_prop) hΨc) (ContinuousOn.smul (by fun_prop) hΨ1c)
  have hder : ∀ u ∈ Ioo (0 : ℝ) T, HasDerivWithinAt Φ (Φ' u) (Ioi u) u := by
    intro u hu
    have hmem : Icc (0 : ℝ) T ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have hΨd : HasDerivAt Ψ (Ψ1 u) u := (h0 u (Ioo_subset_Icc_self hu)).hasDerivAt hmem
    have hΨ1d : HasDerivAt Ψ1 (Ψ2 u) u := (h1 u (Ioo_subset_Icc_self hu)).hasDerivAt hmem
    have hl : HasDerivAt (fun u : ℝ => lam * u) lam u := by simpa using (hasDerivAt_id u).const_mul lam
    have hsn : HasDerivAt (fun u : ℝ => Real.sin (lam * u) / lam) (Real.cos (lam * u)) u := by
      exact (((Real.hasDerivAt_sin (lam * u)).comp u hl).div_const lam).congr_deriv (by field_simp)
    have hcs : HasDerivAt (fun u : ℝ => Real.cos (lam * u) / lam ^ 2) (-(Real.sin (lam * u)) / lam) u := by
      exact (((Real.hasDerivAt_cos (lam * u)).comp u hl).div_const (lam ^ 2)).congr_deriv (by field_simp)
    have := (hsn.smul hΨd).add (hcs.smul hΨ1d)
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [hΦ']
    have e : Real.cos (lam * u) • Ψ u + (Real.cos (lam * u) / lam ^ 2) • Ψ2 u =
        (Real.sin (lam * u) / lam) • Ψ1 u + Real.cos (lam * u) • Ψ u +
          ((Real.cos (lam * u) / lam ^ 2) • Ψ2 u + (-(Real.sin (lam * u)) / lam) • Ψ1 u) := by
      have : (Real.sin (lam * u) / lam) • Ψ1 u + (-(Real.sin (lam * u)) / lam) • Ψ1 u = (0 : E) := by
        rw [← add_smul]
        have h0 : Real.sin (lam * u) / lam + -Real.sin (lam * u) / lam = 0 := by ring
        rw [h0, zero_smul]
      calc _ = (Real.sin (lam * u) / lam) • Ψ1 u + (-(Real.sin (lam * u)) / lam) • Ψ1 u +
            (Real.cos (lam * u) • Ψ u + (Real.cos (lam * u) / lam ^ 2) • Ψ2 u) := by rw [this, zero_add]
        _ = _ := by abel
    exact e.symm
  -- integrability of `Φ'`
  have hint1 : IntervalIntegrable (fun u => Real.cos (lam * u) • Ψ u) volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hT0]
    exact ContinuousOn.smul (by fun_prop) hΨc
  have hmeas2 : AEStronglyMeasurable Ψ2 (volume.restrict (Ioc 0 T)) := by
    refine (stronglyMeasurable_deriv Ψ1).aestronglyMeasurable.congr ?_
    have : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) T)), u ∈ Ioo (0 : ℝ) T := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [this] with u hu
    exact ((h1 u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv
  have hint2 : IntervalIntegrable (fun u => (Real.cos (lam * u) / lam ^ 2) • Ψ2 u) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    refine Integrable.mono' (g := fun _ => A2 / lam ^ 2) (integrable_const _) ?_ ?_
    · exact (by fun_prop : Continuous fun u : ℝ => Real.cos (lam * u) / lam ^ 2).aestronglyMeasurable.smul hmeas2
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun u hu => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlam 2)]
      have hc : |Real.cos (lam * u)| ≤ 1 := Real.abs_cos_le_one _
      have := hA2 u ⟨hu.1.le, hu.2⟩
      calc |Real.cos (lam * u)| / lam ^ 2 * ‖Ψ2 u‖ ≤ 1 / lam ^ 2 * A2 := by
            gcongr
        _ = A2 / lam ^ 2 := by ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT0 hcontΦ hder (hint1.add hint2)
  have hmain : ∫ u in (0 : ℝ)..T, Real.cos (lam * u) • Ψ u =
      Φ T - Φ 0 - ∫ u in (0 : ℝ)..T, (Real.cos (lam * u) / lam ^ 2) • Ψ2 u := by
    rw [eq_sub_iff_add_eq, ← intervalIntegral.integral_add hint1 hint2]
    exact hFTC
  rw [hmain]
  have hΦT : ‖Φ T‖ ≤ A1 / lam ^ 2 := by
    simp only [hΦ, hsin, zero_div, zero_smul, zero_add]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlam 2)]
    calc |Real.cos (lam * T)| / lam ^ 2 * ‖Ψ1 T‖ ≤ 1 / lam ^ 2 * A1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact hA1 T ⟨hT0, le_rfl⟩
      _ = A1 / lam ^ 2 := by ring
  have hΦ0 : ‖Φ 0‖ ≤ A1 / lam ^ 2 := by
    simp only [hΦ, mul_zero, Real.sin_zero, zero_div, zero_smul, zero_add, Real.cos_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlam 2)]
    simpa using (by
      calc 1 / lam ^ 2 * ‖Ψ1 0‖ ≤ 1 / lam ^ 2 * A1 := by
            gcongr; exact hA1 0 ⟨le_rfl, hT0⟩
        _ = A1 / lam ^ 2 := by ring : 1 / lam ^ 2 * ‖Ψ1 0‖ ≤ A1 / lam ^ 2)
  have hI2 : ‖∫ u in (0 : ℝ)..T, (Real.cos (lam * u) / lam ^ 2) • Ψ2 u‖ ≤ T * A2 / lam ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := A2 / lam ^ 2)
      (f := fun u => (Real.cos (lam * u) / lam ^ 2) • Ψ2 u) (fun u hu => by
        rw [uIoc_of_le hT0] at hu
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlam 2)]
        have hc : |Real.cos (lam * u)| ≤ 1 := Real.abs_cos_le_one _
        have h2 := hA2 u ⟨hu.1.le, hu.2⟩
        calc |Real.cos (lam * u)| / lam ^ 2 * ‖Ψ2 u‖ ≤ 1 / lam ^ 2 * A2 := by
              gcongr
          _ = A2 / lam ^ 2 := by ring)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 0)] at this
    calc _ ≤ A2 / lam ^ 2 * (T - 0) := this
      _ = T * A2 / lam ^ 2 := by ring
  calc ‖Φ T - Φ 0 - ∫ u in (0 : ℝ)..T, (Real.cos (lam * u) / lam ^ 2) • Ψ2 u‖
      ≤ ‖Φ T - Φ 0‖ + ‖∫ u in (0 : ℝ)..T, (Real.cos (lam * u) / lam ^ 2) • Ψ2 u‖ := norm_sub_le _ _
    _ ≤ (‖Φ T‖ + ‖Φ 0‖) + T * A2 / lam ^ 2 := add_le_add (norm_sub_le _ _) hI2
    _ ≤ (A1 / lam ^ 2 + A1 / lam ^ 2) + T * A2 / lam ^ 2 := by gcongr
    _ = (2 * A1 + T * A2) / lam ^ 2 := by ring

theorem s103_iter_quot {Fa Fb : Euc d → ℝ} {Fc : Euc d → ℝ} {j : ℕ} (hA : ContDiff ℝ j Fa)
    (hC : ContDiff ℝ j Fc) (hB : ContDiff ℝ j Fb) (h : ℝ) (x : Euc d) :
    iteratedFDeriv ℝ j (fun y => h⁻¹ * (Fa y - Fc y) - Fb y) x =
      h⁻¹ • (iteratedFDeriv ℝ j Fa x - iteratedFDeriv ℝ j Fc x) - iteratedFDeriv ℝ j Fb x := by
  have hAC : ContDiff ℝ j (Fa - Fc) := hA.sub hC
  have e : (fun y => h⁻¹ * (Fa y - Fc y) - Fb y) = (fun y => h⁻¹ • (Fa - Fc) y) - Fb := by
    funext y; simp
  have e2 : (fun y => h⁻¹ • (Fa - Fc) y) = h⁻¹ • (Fa - Fc) := rfl
  rw [e, iteratedFDeriv_sub_apply (hAC.const_smul h⁻¹).contDiffAt hB.contDiffAt, e2,
    iteratedFDeriv_const_smul_apply hAC.contDiffAt,
    iteratedFDeriv_sub_apply hA.contDiffAt hC.contDiffAt]

theorem s103_hasDeriv_iter {Fa Fb : ℝ → Euc d → ℝ} {T0 : ℝ} {j : ℕ}
    (hcdA : ∀ τ ∈ Set.Icc (0 : ℝ) T0, ContDiff ℝ j (Fa τ))
    (hcdB : ∀ τ ∈ Set.Icc (0 : ℝ) T0, ContDiff ℝ j (Fb τ))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      t + h ∈ Set.Icc (0 : ℝ) T0 → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (Fa (t + h) y - Fa t y) - Fb t y) x‖ ≤ ε) (x : Euc d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T0, HasDerivWithinAt (fun τ => iteratedFDeriv ℝ j (Fa τ) x)
      (iteratedFDeriv ℝ j (Fb t) x) (Set.Icc 0 T0) t := by
  intro t ht
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := hdiff t ht c hc
  have hev : ∀ᶠ t' in 𝓝[Set.Icc 0 T0] t, t' ∈ Set.Icc (0 : ℝ) T0 ∧ |t' - t| < δ := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [Metric.ball_mem_nhds t hδ] with t' ht' hmem
    exact ⟨hmem, by simpa [Real.dist_eq] using ht'⟩
  filter_upwards [hev] with t' ⟨ht'm, ht'd⟩
  by_cases h0 : t' - t = 0
  · have : t' = t := by linarith
    subst this; simp
  · have hq := hδ' (t' - t) h0 ht'd (by simpa using ht'm) x
    have ht'm' : t + (t' - t) ∈ Set.Icc (0 : ℝ) T0 := by simpa using ht'm
    rw [s103_iter_quot (hcdA _ ht'm') (hcdA _ ht) (hcdB _ ht) _ x] at hq
    have hq' : ‖iteratedFDeriv ℝ j (Fa t') x - iteratedFDeriv ℝ j (Fa t) x -
        (t' - t) • iteratedFDeriv ℝ j (Fb t) x‖ ≤ c * ‖t' - t‖ := by
      have e : iteratedFDeriv ℝ j (Fa t') x - iteratedFDeriv ℝ j (Fa t) x -
          (t' - t) • iteratedFDeriv ℝ j (Fb t) x =
          (t' - t) • ((t' - t)⁻¹ • (iteratedFDeriv ℝ j (Fa (t + (t' - t))) x - iteratedFDeriv ℝ j (Fa t) x) -
            iteratedFDeriv ℝ j (Fb t) x) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ h0, one_smul]
        simp
      rw [e, norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa [add_sub_cancel] using hq) (abs_nonneg _)
    simpa using hq'

end HRS.MS.R2WinOrb

end
