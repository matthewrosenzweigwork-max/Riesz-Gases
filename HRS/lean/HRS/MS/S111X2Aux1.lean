import Mathlib

/-!
# S11.1 X2, scalar calculus (packets E06, E08)

`s111x2_sharp_energy` (E06): `E' = -2 ν D`, `λ V ≤ D`, `η V ≤ E ≤ V` give `E t ≤ e^{-2νλ t} E 0` and
`V t ≤ η⁻¹ e^{-2νλ t} V 0`.  `s111x2_derivative_from_two_averages` (E08): the two-average derivative bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace HRS.MS.S111X2

/-- FTC for an absolutely continuous function on a subinterval of `[0,T]`. -/
theorem s111x2_integral_deriv {g g' : ℝ → ℝ} {T a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), HasDerivAt g (g' t) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    ∫ x in a..b, g' x = g b - g a := by
  have hsub : uIcc a b ⊆ uIcc 0 T := by
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]; exact Icc_subset_Icc ha hb
  rw [← (hg.mono hsub).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Icc] at hd
  filter_upwards [hd] with x hx hxm
  rw [uIoc_of_le hab] at hxm
  rw [(hx ⟨ha.trans hxm.1.le, hxm.2.trans hb⟩).deriv]

/-- Sign of the integral of an a.e. signed function. -/
theorem s111x2_integral_nonneg {g' : ℝ → ℝ} {T a b : ℝ}
    (hle : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), 0 ≤ g' t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) : 0 ≤ ∫ x in a..b, g' x := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict hab
  exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc ha hb) hle

/-- An absolutely continuous function with a.e. nonpositive derivative decreases. -/
theorem s111x2_ac_anti {g g' : ℝ → ℝ} {T : ℝ} (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), HasDerivAt g (g' t) t)
    (hle : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), g' t ≤ 0) :
    ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → g b ≤ g a := by
  intro a b ha hab hb
  have h1 := s111x2_integral_deriv hg hd ha hab hb
  have h2 : 0 ≤ ∫ x in a..b, -g' x :=
    s111x2_integral_nonneg (by filter_upwards [hle] with t ht using neg_nonneg.2 ht) ha hab hb
  rw [intervalIntegral.integral_neg] at h2; linarith

theorem s111x2_ac_le_start {g g' : ℝ → ℝ} {T : ℝ} (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), HasDerivAt g (g' t) t)
    (hle : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), g' t ≤ 0) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, g t ≤ g 0 := fun t ht => s111x2_ac_anti hg hd hle 0 t le_rfl ht.1 ht.2

/-- **E06** sharp scalar energy decay. -/
theorem s111x2_sharp_energy (T nu lam eta : ℝ)
    (hT : 0 ≤ T) (hnu : 0 < nu) (hlam : 0 < lam) (heta : 0 < eta)
    (E V D : ℝ → ℝ)
    (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hD : IntegrableOn D (Set.Icc 0 T))
    (hV : ∀ t ∈ Set.Icc 0 T, 0 ≤ V t ∧ eta * V t ≤ E t ∧ E t ≤ V t)
    (hP : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), lam * V t ≤ D t)
    (hdE : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), HasDerivAt E (-2 * nu * D t) t) :
    ∀ t ∈ Set.Icc 0 T,
      E t ≤ Real.exp (-2 * nu * lam * t) * E 0 ∧
      V t ≤ eta⁻¹ * Real.exp (-2 * nu * lam * t) * V 0 := by
  have _ := hD
  set c : ℝ := 2 * nu * lam with hc
  have hcpos : 0 < c := by positivity
  let g : ℝ → ℝ := fun t => Real.exp (c * t) * E t
  have hexp : AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (c * t)) 0 T :=
    (ContDiff.contDiffOn (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => Real.exp (c * t)))).absolutelyContinuousOnInterval
  have hg : AbsolutelyContinuousOnInterval g 0 T := hexp.mul hE
  have hdg : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      HasDerivAt g (Real.exp (c * t) * (c * E t + (-2 * nu * D t))) t := by
    filter_upwards [hdE] with t ht
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (c * t)) (Real.exp (c * t) * c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).exp
    have := h1.mul ht
    convert this using 1; ring
  have hle : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      Real.exp (c * t) * (c * E t + (-2 * nu * D t)) ≤ 0 := by
    have hmem : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), t ∈ Icc (0:ℝ) T := ae_restrict_mem measurableSet_Icc
    filter_upwards [hP, hmem] with t hPt hmt
    obtain ⟨_, _, h3⟩ := hV t hmt
    have : c * E t + (-2 * nu * D t) ≤ 0 := by
      have : 2 * nu * (lam * V t) ≤ 2 * nu * D t := by gcongr
      have h4 : c * E t ≤ c * V t := by gcongr
      rw [hc] at h4 ⊢; nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have hmain := s111x2_ac_le_start hg hdg hle hT
  intro t ht
  have hgt := hmain t ht
  simp only [g, mul_zero, Real.exp_zero, one_mul] at hgt
  have hEt : E t ≤ Real.exp (-2 * nu * lam * t) * E 0 := by
    have : Real.exp (-2 * nu * lam * t) = (Real.exp (c * t))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; rw [hc]; ring
    rw [this]
    have hp := Real.exp_pos (c * t)
    rw [← div_eq_inv_mul, le_div_iff₀ hp]; linarith
  refine ⟨hEt, ?_⟩
  obtain ⟨hV0, h20, _⟩ := hV t ht
  obtain ⟨_, _, h30⟩ := hV 0 ⟨le_rfl, hT⟩
  have hexp0 := Real.exp_pos (-2 * nu * lam * t)
  have : eta * V t ≤ Real.exp (-2 * nu * lam * t) * V 0 := by
    calc eta * V t ≤ E t := h20
      _ ≤ _ := hEt
      _ ≤ _ := by gcongr
  calc V t = eta⁻¹ * (eta * V t) := by field_simp
    _ ≤ eta⁻¹ * (Real.exp (-2 * nu * lam * t) * V 0) := by gcongr
    _ = _ := by ring

/-- **E08** derivative bound from two time averages. -/
theorem s111x2_derivative_from_two_averages (T nu kappa eta : ℝ)
    (hT : 1 ≤ T) (hnu : 0 < nu) (hkappa : 0 < kappa) (heta : 0 < eta)
    (E D Fenergy Vg : ℝ → ℝ)
    (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hD : AbsolutelyContinuousOnInterval D 0 T)
    (hF : ContinuousOn Fenergy (Set.Icc 0 T))
    (hpos : ∀ t ∈ Set.Icc 0 T,
      0 ≤ E t ∧ 0 ≤ D t ∧ 0 ≤ Fenergy t ∧ eta * Vg t ≤ Fenergy t)
    (hmono : AntitoneOn Fenergy (Set.Icc 0 T))
    (hdE : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), HasDerivAt E (-2 * nu * D t) t)
    (hdD : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), HasDerivAt D (-2 / nu * Fenergy t) t)
    (hdec : ∀ t ∈ Set.Icc 0 T, E t ≤ Real.exp (-2 * kappa * t) * E 0) :
    ∀ t ∈ Set.Icc 1 T,
      Fenergy t ≤ E (t - 1) ∧
      Vg t ≤ eta⁻¹ * Real.exp (-2 * kappa * (t - 1)) * E 0 := by
  intro t ht
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hmem : ∀ᵐ x ∂(volume.restrict (Icc 0 T)), x ∈ Icc (0:ℝ) T := ae_restrict_mem measurableSet_Icc
  -- D is decreasing
  have hDle : ∀ᵐ x ∂(volume.restrict (Icc 0 T)), -2 / nu * Fenergy x ≤ 0 := by
    filter_upwards [hmem] with x hx
    have := (hpos x hx).2.2.1
    have : -2 / nu ≤ 0 := by
      have : 0 < 2 / nu := by positivity
      rw [neg_div]; linarith
    exact mul_nonpos_of_nonpos_of_nonneg this (hpos x hx).2.2.1
  have hDanti := s111x2_ac_anti hD hdD hDle
  have ht1 : 0 ≤ t - 1 := by linarith [ht.1]
  have htT : t ≤ T := ht.2
  have hcD : ContinuousOn D (Icc 0 T) := by
    have := hD.continuousOn; rwa [uIcc_of_le hT0] at this
  -- first average
  have hA : E (t - 1/2) - E (t - 1) ≤ (-2 * nu * D (t - 1/2)) * (1/2) := by
    have h1 := s111x2_integral_deriv hE hdE (a := t - 1) (b := t - 1/2) ht1 (by linarith) (by linarith)
    have h2 : ∫ x in (t - 1)..(t - 1/2), (-2 * nu * D x) ≤
        ∫ x in (t - 1)..(t - 1/2), (-2 * nu * D (t - 1/2)) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith)]
        exact (continuousOn_const.mul (hcD.mono (Icc_subset_Icc ht1 (by linarith))))
      · exact intervalIntegrable_const
      · intro x hx
        have := hDanti x (t - 1/2) (by linarith [hx.1]) hx.2 (by linarith)
        nlinarith
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, show t - 1/2 - (t - 1) = 1/2 by ring] at h2
    linarith
  have hB : D t - D (t - 1/2) ≤ (-2 / nu * Fenergy t) * (1/2) := by
    have h1 := s111x2_integral_deriv hD hdD (a := t - 1/2) (b := t) (by linarith) (by linarith) htT
    have h2 : ∫ x in (t - 1/2)..t, (-2 / nu * Fenergy x) ≤
        ∫ x in (t - 1/2)..t, (-2 / nu * Fenergy t) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith)]
        exact (continuousOn_const.mul (hF.mono (Icc_subset_Icc (by linarith) htT)))
      · exact intervalIntegrable_const
      · intro x hx
        have := hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith, htT⟩ hx.2
        have hn : -2 / nu ≤ 0 := by
          have : 0 < 2 / nu := by positivity
          rw [neg_div]; linarith
        nlinarith
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, show t - (t - 1/2) = 1/2 by ring] at h2
    linarith
  have hE0 := (hpos (t - 1/2) ⟨by linarith, by linarith⟩).1
  have hDt := (hpos t ⟨by linarith, htT⟩).2.1
  have hF1 : Fenergy t ≤ E (t - 1) := by
    -- Fenergy t ≤ nu * (D (t-1/2) - D t)
    have hq : 0 < 2 / nu := by positivity
    have hB' : (Fenergy t) / nu ≤ D (t - 1/2) - D t := by
      have : -2 / nu * Fenergy t * (1/2) = -(Fenergy t / nu) := by field_simp
      linarith
    have hB'' : Fenergy t ≤ nu * (D (t - 1/2) - D t) := by
      rw [div_le_iff₀ hnu] at hB'; linarith
    nlinarith
  refine ⟨hF1, ?_⟩
  have h2 : eta * Vg t ≤ Real.exp (-2 * kappa * (t - 1)) * E 0 :=
    ((hpos t ⟨by linarith, htT⟩).2.2.2).trans (hF1.trans (hdec (t - 1) ⟨ht1, by linarith⟩))
  calc Vg t = eta⁻¹ * (eta * Vg t) := by field_simp
    _ ≤ eta⁻¹ * (Real.exp (-2 * kappa * (t - 1)) * E 0) := by gcongr
    _ = _ := by ring

end HRS.MS.S111X2
