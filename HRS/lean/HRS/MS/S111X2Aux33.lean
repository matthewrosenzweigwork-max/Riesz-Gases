import HRS.MS.S111X2Aux32

/-!
# S11.1 X2, packet H01 (part 1): the two-average bound without the decay hypothesis

`s111x2_fenergy_le`: the scalar argument of E08 (`Fenergy t ≤ E (t-1)` for `t ≥ 1`) does not use the decay of `E`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace HRS.MS.S111X2

theorem s111x2_fenergy_le (T nu : ℝ) (hT : 1 ≤ T) (hnu : 0 < nu) (E D Fenergy : ℝ → ℝ)
    (hE : AbsolutelyContinuousOnInterval E 0 T) (hD : AbsolutelyContinuousOnInterval D 0 T)
    (hF : ContinuousOn Fenergy (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ E t ∧ 0 ≤ D t ∧ 0 ≤ Fenergy t)
    (hmono : AntitoneOn Fenergy (Icc 0 T))
    (hdE : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), HasDerivAt E (-2 * nu * D t) t)
    (hdD : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), HasDerivAt D (-2 / nu * Fenergy t) t) :
    ∀ t ∈ Icc 1 T, Fenergy t ≤ E (t - 1) := by
  intro t ht
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hmem : ∀ᵐ x ∂(volume.restrict (Icc 0 T)), x ∈ Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  have hDle : ∀ᵐ x ∂(volume.restrict (Icc 0 T)), -2 / nu * Fenergy x ≤ 0 := by
    filter_upwards [hmem] with x hx
    have : -2 / nu ≤ 0 := by
      have : 0 < 2 / nu := by positivity
      rw [neg_div]; linarith
    exact mul_nonpos_of_nonpos_of_nonneg this (hpos x hx).2.2
  have hDanti := s111x2_ac_anti hD hdD hDle
  have ht1 : 0 ≤ t - 1 := by linarith [ht.1]
  have htT : t ≤ T := ht.2
  have hcD : ContinuousOn D (Icc 0 T) := by
    have := hD.continuousOn; rwa [uIcc_of_le hT0] at this
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
  have hq : 0 < 2 / nu := by positivity
  have hB' : (Fenergy t) / nu ≤ D (t - 1/2) - D t := by
    have : -2 / nu * Fenergy t * (1/2) = -(Fenergy t / nu) := by field_simp
    linarith
  have hB'' : Fenergy t ≤ nu * (D (t - 1/2) - D t) := by
    rw [div_le_iff₀ hnu] at hB'; linarith
  nlinarith

end HRS.MS.S111X2
