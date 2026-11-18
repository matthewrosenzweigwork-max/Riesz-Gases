import HRS.MS.Fp81S21WindowSupMeas2

/-! Conversion of a continuous window's lower-integral bound to a moment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21

/-- The sixth-root bound for the extended supremum gives the sixth moment
of the real supremum. -/
theorem fp81s21_window_sup_moment6 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → ℝ) (b T M : ℝ) (hbT : b ≤ T) (hM : 0 ≤ M)
    (hm : ∀ t ∈ Icc b T, AEMeasurable (X t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc b T))
    (hbound : (∫⁻ ω, (⨆ t : Icc b T, ‖X t ω‖ₑ) ^ (6 : ℝ) ∂P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal M) :
    fp81s21_Moment6 P (fun ω => ⨆ t : Icc b T, ‖X t ω‖) (M ^ 6) := by
  classical
  letI : Nonempty (Icc b T) := ⟨⟨b, ⟨le_rfl, hbT⟩⟩⟩
  obtain ⟨D, hD, hDs, hDd, hpath, hmeas⟩ :=
    fp81s21_window_sup_measurable P X b T hbT hm hc
  have heq : ∀ᵐ ω ∂P,
      ENNReal.ofReal (‖⨆ t : Icc b T, ‖X t ω‖‖ ^ 6) =
        (⨆ t : Icc b T, ‖X t ω‖ₑ) ^ (6 : ℝ) := by
    filter_upwards [hc, hpath] with ω hω hp
    have hs : 0 ≤ (⨆ t : Icc b T, ‖X t ω‖) := Real.iSup_nonneg fun t => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hs, ENNReal.ofReal_pow hs, ← ENNReal.rpow_natCast]
    rw [hp.2, ← fp81s21_window_enorm_sup_dense hω hDs hDd]
    norm_num
  have hpow : (∫⁻ ω, (⨆ t : Icc b T, ‖X t ω‖ₑ) ^ (6 : ℝ) ∂P) ≤
      ENNReal.ofReal (M ^ 6) := by
    have h := ENNReal.rpow_le_rpow hbound (by norm_num : (0 : ℝ) ≤ 6)
    rw [← ENNReal.rpow_mul] at h
    norm_num at h
    simpa [ENNReal.rpow_natCast, ENNReal.ofReal_pow hM] using h
  apply fp81s21_moment6_of_lintegral P _ _ hmeas (pow_nonneg hM 6)
  rw [lintegral_congr_ae heq]
  exact hpow

#print axioms fp81s21_window_sup_moment6
end HRS.Fp81.S21
end
