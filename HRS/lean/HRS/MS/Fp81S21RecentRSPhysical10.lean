import HRS.MS.Fp81S21RecentRSPhysical9
import HRS.MS.Fp81S21RecentRSPhysical8

/-! Passage from physical window corrections to the signed joint comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21

/-- Intermediate assembly on the supplied RS records. The two value events are
provided by the physical particle and Gaussian adapters. -/
theorem fp81s21_recentRS_window_signed_of_values
    {Ω Ω' C D J ED EJ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
    [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : ℝ} {AdN : Ω → ℝ → ED →L[ℝ] ℝ} {FdN : Ω → ℝ → ED}
    {AjN : Ω → ℝ → EJ →L[ℝ] ℝ} {FjN : Ω → ℝ → EJ}
    {AdG : Ω' → ℝ → ED →L[ℝ] ℝ} {FdG : Ω' → ℝ → ED}
    {AjG : Ω' → ℝ → EJ →L[ℝ] ℝ} {FjG : Ω' → ℝ → EJ}
    (WN : fp81s21_WindowRS μ T AdN FdN AjN FjN)
    (WG : fp81s21_WindowRS ν T AdG FdG AjG FjG) (b t : ℝ)
    (yN : Ω → C) (dN : Ω → D) (jN : Ω → J)
    (yG : Ω' → C) (dG : Ω' → D) (jG : Ω' → J)
    (hmN : Measurable (fun ω => (yN ω, (dN ω, jN ω))))
    (hmG : Measurable (fun ω => (yG ω, (dG ω, jG ω))))
    (hdN : MemLp dN 2 μ) (hjN : MemLp jN 2 μ)
    (hdG : MemLp dG 2 ν) (hjG : MemLp jG 2 ν)
    {KD KJ e M η : ℝ} (hKD : 0 < KD) (hKJ : 0 < KJ)
    (he : 0 ≤ e) (hM : 0 ≤ M) (hη : 0 < η)
    (FD : fp81s21_RecentRSKernel C D KD) (FJ : fp81s21_RecentRSKernel C J KJ)
    (hW : HRS.wassersteinE 2 (μ.map (fun ω => (yN ω, (dN ω, jN ω))))
      (ν.map (fun ω => (yG ω, (dG ω, jG ω)))) ≤ ENNReal.ofReal e)
    (hMoment : (∫ ω, (‖dG ω‖ ^ 2 + ‖jG ω‖ ^ 2) ∂ν) ≤ M)
    (hN : ∀ᵐ ω ∂μ, WN.drift.value b t ω = FD.kernel (yN ω) (dN ω) ∧
      WN.covariance.value b t ω = FJ.kernel (yN ω) (jN ω))
    (hG : ∀ᵐ ω ∂ν, WG.drift.value b t ω = FD.kernel (yG ω) (dG ω) ∧
      WG.covariance.value b t ω = FJ.kernel (yG ω) (jG ω)) :
    |fp81s21_WindowRS_corr WN b t - fp81s21_WindowRS_corr WG b t| ≤
      (KD + KJ / 2) * (1 + Real.sqrt M) * (e + η) := by
  exact fp81s21_recentRS_signed_of_values μ ν yN dN jN yG dG jG
    (WN.drift.value b t) (WN.covariance.value b t)
    (WG.drift.value b t) (WG.covariance.value b t)
    hmN hmG hdN hjN hdG hjG hKD hKJ he hM hη FD FJ hW hMoment hN hG

#print axioms fp81s21_recentRS_window_signed_of_values
end HRS.Fp81.S21
