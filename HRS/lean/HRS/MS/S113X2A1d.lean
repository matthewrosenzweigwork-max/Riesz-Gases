import HRS.MS.S113X2A1c

/-!
# S11.3 X2 part A1d: the stopped Itô integral has weighted mean zero
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

theorem s113a_weighted_mean_zero {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) {Ψ : ℝ → Ω → ι → ℝ}
    (hΨ : IsProgressiveL2 P ℱ Ψ) (h0 : ∀ s ≤ -1, ∀ ζ, Ψ s ζ = 0) {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) {ξ : Ω → ℝ} (hξ : Measurable[ℱ (-1)] ξ) {C : ℝ}
    (hC : ∀ ζ, |ξ ζ| ≤ C) (T : ℝ) :
    Integrable (fun ζ => ξ ζ * localItoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ) P ∧
      ∫ ζ, ξ ζ * localItoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ ∂P = 0 := by
  have hS : IsProgressiveL2 P ℱ (stopIntegrand Ψ τ) := hΨ.stopIntegrand hτ
  have h0S : ∀ s ≤ (-1 : ℝ), ∀ ζ, stopIntegrand Ψ τ s ζ = 0 := by
    intro s hs ζ
    simp [stopIntegrand, Set.indicator, h0 s hs ζ]
  have heq := localItoIntegral_eq_itoIntegral hW hS
  have hmul := itoIntegral_mul_meas hW hS h0S hξ hC T
  have hL2 := isProgressiveL2_mul_meas hS hξ h0S hC
  have hξm : Measurable ξ := hξ.mono (ℱ.le _) le_rfl
  have hint : Integrable (itoIntegral P ℱ W (stopIntegrand Ψ τ) T) P :=
    (memLp_two_itoIntegral hW hS T).integrable one_le_two
  have hint2 : Integrable (fun ζ => ξ ζ * itoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ) P :=
    hint.bdd_mul hξm.aestronglyMeasurable (ae_of_all _ fun ζ => by simpa using hC ζ)
  have hae : (fun ζ => ξ ζ * localItoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ)
      =ᵐ[P] fun ζ => itoIntegral P ℱ W (fun s ζ k => ξ ζ * stopIntegrand Ψ τ s ζ k) T ζ := by
    filter_upwards [heq, hmul] with ζ h1 h2
    rw [h2, h1 T]
  have hae2 : (fun ζ => ξ ζ * localItoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ)
      =ᵐ[P] fun ζ => ξ ζ * itoIntegral P ℱ W (stopIntegrand Ψ τ) T ζ := by
    filter_upwards [heq] with ζ h1
    rw [h1 T]
  refine ⟨hint2.congr hae2.symm, ?_⟩
  rw [integral_congr_ae hae]
  exact integral_itoIntegral hW hL2 T

end HRS.MS.S113X2

end
