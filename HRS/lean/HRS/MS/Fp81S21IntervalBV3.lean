import HRS.MS.Fp81S21IntervalBV2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Integral controls for the generic interval-to-BV transport. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H K : ℝ} (hH : 0 ≤ H)

/-- Integral domination supplies the scalar control used by the BV transport. -/
def fp81s21_integralIntervalBVData
    (Δ : ℝ → ℝ → X →L[ℝ] E) (w : X → ℝ → ℝ)
    (hz : Δ 0 0 = 0)
    (ha : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, s ≤ t →
      Δ 0 t = Δ 0 s + Δ s t)
    (hc : ∀ x, ContinuousOn (fun t => Δ 0 t x) (Icc 0 H))
    (hi : ∀ x (s : ℝ), s ∈ Icc (0 : ℝ) H → ∀ t ∈ Icc (0 : ℝ) H,
      IntervalIntegrable (w x) volume s t)
    (hn : ∀ x, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) H)), 0 ≤ w x t)
    (hb : ∀ x (s : ℝ), s ∈ Icc (0 : ℝ) H → ∀ t ∈ Icc (0 : ℝ) H, s ≤ t →
      ‖Δ s t x‖ ≤ ∫ z in s..t, w x z)
    (ht : ∀ x, (∫ z in (0 : ℝ)..H, w x z) ≤ K * ‖x‖) :
    fp81s21_IntervalBVData (X := X) (E := E) (H := H) K where
  delta := Δ
  zero := hz
  add := ha
  cont := hc
  control := fun x t => ∫ z in (0 : ℝ)..t, w x z
  control_mono := by
    intro x s hs t ht' hst
    have hs0 : (0 : ℝ) ∈ Icc 0 H := ⟨le_rfl, hH⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hi x 0 hs0 s hs) (hi x s hs t ht')
    have hnon : 0 ≤ ∫ z in s..t, w x z := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hst
      exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.1 ht'.2) (hn x)
    linarith
  inc_le := by
    intro x s hs t ht' hst
    have hs0 : (0 : ℝ) ∈ Icc 0 H := ⟨le_rfl, hH⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hi x 0 hs0 s hs) (hi x s hs t ht')
    linarith [hb x s hs t ht' hst]
  total_le := by
    intro x
    simpa using ht x

#print axioms fp81s21_integralIntervalBVData
end HRS.Fp81.S21
end
