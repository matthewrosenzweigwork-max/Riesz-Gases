import HRS.MS.SuppU8Aux3

/-!
# Worker U8 aux 5: far-field estimate `∫_{‖y‖ ≥ ρ} ‖y‖^{-d-α} (1 + ‖x + j y‖)^{-b} dy`
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

variable {d : ℕ}

theorem u8_comp_affine_integrable (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : Integrable G)
    (x : EuclideanSpace ℝ (Fin d)) (c : ℝ) (hc : c ≠ 0) :
    Integrable (fun y => G (x + c • y)) := by
  have h1 : Integrable (fun z => G (x + z)) := hG.comp_add_left x
  exact h1.comp_smul hc

theorem u8_comp_affine_integral (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    ∫ y, G (x + c • y) = |(c ^ d)⁻¹| * ∫ z, G z := by
  have h1 := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun z => G (x + z)) c
  rw [finrank_euclideanSpace_fin, smul_eq_mul, integral_add_left_eq_self] at h1
  exact h1

theorem u8_half_rpow (n b : ℝ) (hn : 0 < n) : (n / 2) ^ (-b) = 2 ^ b * n ^ (-b) := by
  rw [div_eq_mul_inv, Real.mul_rpow hn.le (by norm_num), Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]

/-- The far-field term for one shift `j`. -/
theorem u8_far_term (hd : 1 ≤ d) (b α : ℝ) (hb : 0 < b) (hbd : b < d) (hα : 0 < α)
    (x : EuclideanSpace ℝ (Fin d)) (j : ℤ) (n ρ : ℝ) (hn : n = 1 + ‖x‖) (hρ : 0 < ρ) :
    Integrable ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b))) ∧
    ∫ y, ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b))) y ≤
      u8_cd d * (2 ^ b * n ^ (-b) * (ρ ^ (-α) / α) +
        ρ ^ (-((d : ℝ) + α)) * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b))) := by
  have : NeZero d := ⟨by omega⟩
  have hnpos : 0 < n := by rw [hn]; positivity
  have hcd := u8_cd_pos hd
  have hdb : 0 < (d : ℝ) - b := by linarith
  obtain ⟨hfarI, hfarV⟩ := u8_far_int (d := d) hd α ρ hα hρ
  have hK : (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ (-(d : ℝ) - α)) =
      fun y => ‖y‖ ^ (-((d : ℝ) + α)) := by
    funext y; rw [neg_add']
  rw [hK] at hfarI hfarV
  set T1 : EuclideanSpace ℝ (Fin d) → ℝ := (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
    (fun y => ‖y‖ ^ (-((d : ℝ) + α))) with hT1
  have hrhs_nonneg : 0 ≤ ρ ^ (-((d : ℝ) + α)) * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b)) := by
    positivity
  have hb1 : 1 ≤ (2 : ℝ) ^ b := Real.one_le_rpow (by norm_num) hb.le
  by_cases hj : j = 0
  · subst hj
    have hF : ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + ((0 : ℤ) : ℝ) • y‖) ^ (-b))) =
        fun y => n ^ (-b) * T1 y := by
      funext y
      by_cases hy : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ
      · simp only [hT1, indicator_of_mem hy, Int.cast_zero, zero_smul, add_zero, ← hn]
        ring
      · simp [hT1, indicator_of_notMem hy]
    rw [hF]
    refine ⟨hfarI.const_mul _, ?_⟩
    rw [integral_const_mul, hfarV]
    have : n ^ (-b) * (u8_cd d * (ρ ^ (-α) / α)) ≤ u8_cd d * (2 ^ b * n ^ (-b) * (ρ ^ (-α) / α)) := by
      have h0 : 0 ≤ u8_cd d * (n ^ (-b) * (ρ ^ (-α) / α)) := by positivity
      nlinarith [mul_nonneg h0 (sub_nonneg.2 hb1)]
    have h2 : 0 ≤ u8_cd d * (ρ ^ (-((d : ℝ) + α)) * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b))) :=
      mul_nonneg hcd.le hrhs_nonneg
    rw [mul_add]
    linarith
  · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    obtain ⟨hnearI, hnearV⟩ := u8_near_int (d := d) hd ((d : ℝ) - b) (n / 2) hdb (by positivity)
    have hexp : ((d : ℝ) - b) - d = -b := by ring
    rw [hexp] at hnearI hnearV
    set G : EuclideanSpace ℝ (Fin d) → ℝ :=
      (ball (0 : EuclideanSpace ℝ (Fin d)) (n / 2)).indicator (fun z => ‖z‖ ^ (-b)) with hG
    have hGI : Integrable G := (integrable_indicator_iff measurableSet_ball).2 hnearI
    have hGV : ∫ z, G z = u8_cd d * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b)) := by
      rw [hG, integral_indicator measurableSet_ball, hnearV]
    set T2 : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun y => ρ ^ (-((d : ℝ) + α)) * G (x + (j : ℝ) • y) with hT2
    have hT2I : Integrable T2 :=
      (u8_comp_affine_integrable G hGI x (j : ℝ) hjR).const_mul _
    have hT2V : ∫ y, T2 y ≤ u8_cd d * (ρ ^ (-((d : ℝ) + α)) *
        ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b))) := by
      rw [hT2, integral_const_mul, u8_comp_affine_integral G x (j : ℝ), hGV]
      have hjd : |((j : ℝ) ^ d)⁻¹| ≤ 1 := by
        rw [abs_inv, inv_le_one₀ (abs_pos.2 (pow_ne_zero _ hjR))]
        rw [abs_pow]
        apply one_le_pow₀
        have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
        have h2 : (1 : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast this
        simpa using h2
      have hnn : 0 ≤ ρ ^ (-((d : ℝ) + α)) * (u8_cd d * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b))) := by
        have : 0 ≤ u8_cd d * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b)) := by positivity
        positivity
      calc ρ ^ (-((d : ℝ) + α)) * (|((j : ℝ) ^ d)⁻¹| * (u8_cd d * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b))))
          ≤ ρ ^ (-((d : ℝ) + α)) * (1 * (u8_cd d * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_right hjd (by positivity)
        _ = _ := by ring
    -- the pointwise domination
    set Fj : EuclideanSpace ℝ (Fin d) → ℝ := (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b)) with hFj
    have hFnn : ∀ y, 0 ≤ Fj y := by
      intro y; rw [hFj]
      apply indicator_nonneg
      intro y _
      positivity
    have hmeas : Measurable Fj := by
      rw [hFj]
      refine Measurable.indicator ?_ (measurableSet_ball.compl)
      fun_prop
    set y0 : EuclideanSpace ℝ (Fin d) := ((j : ℝ)⁻¹) • (-x) with hy0
    have hae : ∀ᵐ y : EuclideanSpace ℝ (Fin d) ∂volume, y ≠ y0 := by
      have := (Set.countable_singleton y0).ae_notMem (volume : Measure (EuclideanSpace ℝ (Fin d)))
      filter_upwards [this] with y hy using by simpa using hy
    have hdom : ∀ᵐ y : EuclideanSpace ℝ (Fin d) ∂volume, Fj y ≤ 2 ^ b * n ^ (-b) * T1 y + T2 y := by
      filter_upwards [hae] with y hy
      have hw : x + (j : ℝ) • y ≠ 0 := by
        intro h
        apply hy
        rw [hy0]
        have : (j : ℝ) • y = -x := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
        rw [← this, smul_smul, inv_mul_cancel₀ hjR, one_smul]
      have hwpos : 0 < ‖x + (j : ℝ) • y‖ := norm_pos_iff.2 hw
      have hT1nn : 0 ≤ T1 y := by
        rw [hT1]; apply indicator_nonneg; intro y _; positivity
      have hT2nn : 0 ≤ T2 y := by
        rw [hT2]
        apply mul_nonneg (by positivity)
        rw [hG]; apply indicator_nonneg; intro z _; positivity
      by_cases hyb : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ
      · have hyr : ρ ≤ ‖y‖ := by simpa using hyb
        have hFy : Fj y = ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b) := by
          rw [hFj]; exact indicator_of_mem hyb _
        have hT1y : T1 y = ‖y‖ ^ (-((d : ℝ) + α)) := by
          rw [hT1]; exact indicator_of_mem hyb _
        rw [hFy]
        by_cases hcase : n / 2 ≤ ‖x + (j : ℝ) • y‖
        · have h1 : (1 + ‖x + (j : ℝ) • y‖) ^ (-b) ≤ (n / 2) ^ (-b) := by
            apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          rw [u8_half_rpow n b hnpos] at h1
          rw [hT1y]
          have : ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b) ≤
              ‖y‖ ^ (-((d : ℝ) + α)) * (2 ^ b * n ^ (-b)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          nlinarith [hT2nn]
        · push Not at hcase
          have hGy : G (x + (j : ℝ) • y) = ‖x + (j : ℝ) • y‖ ^ (-b) := by
            rw [hG]; exact indicator_of_mem (by simpa using hcase) _
          have h1 : (1 + ‖x + (j : ℝ) • y‖) ^ (-b) ≤ ‖x + (j : ℝ) • y‖ ^ (-b) :=
            Real.rpow_le_rpow_of_nonpos hwpos (by linarith) (by linarith)
          have h2 : ‖y‖ ^ (-((d : ℝ) + α)) ≤ ρ ^ (-((d : ℝ) + α)) :=
            Real.rpow_le_rpow_of_nonpos hρ hyr (by
              have : (0 : ℝ) < (d : ℝ) + α := by positivity
              linarith)
          have h3 : ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b) ≤
              ρ ^ (-((d : ℝ) + α)) * ‖x + (j : ℝ) • y‖ ^ (-b) :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
          have h4 : T2 y = ρ ^ (-((d : ℝ) + α)) * ‖x + (j : ℝ) • y‖ ^ (-b) := by
            rw [hT2]; simp only; rw [hGy]
          have h5 : 0 ≤ 2 ^ b * n ^ (-b) * T1 y := by positivity
          linarith
      · have hFy : Fj y = 0 := by rw [hFj]; exact indicator_of_notMem hyb _
        rw [hFy]
        have h5 : 0 ≤ 2 ^ b * n ^ (-b) * T1 y := by positivity
        linarith
    have hmaj : Integrable (fun y => 2 ^ b * n ^ (-b) * T1 y + T2 y) :=
      (hfarI.const_mul _).add hT2I
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
      filter_upwards [hdom] with y hy
      rw [Real.norm_of_nonneg (hFnn y)]
      exact hy
    · calc ∫ y, Fj y ≤ ∫ y, (2 ^ b * n ^ (-b) * T1 y + T2 y) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall hFnn) hmaj hdom
        _ = 2 ^ b * n ^ (-b) * (∫ y, T1 y) + ∫ y, T2 y := by
            rw [integral_add (hfarI.const_mul _) hT2I, integral_const_mul]
        _ ≤ _ := by
            rw [hfarV, mul_add]
            have : 2 ^ b * n ^ (-b) * (u8_cd d * (ρ ^ (-α) / α)) =
                u8_cd d * (2 ^ b * n ^ (-b) * (ρ ^ (-α) / α)) := by ring
            linarith

end HRS.U8
