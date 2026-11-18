import HRS.MH.FeatureMap3

/-!
# Relocated proofs for `HRS/Energy/FeatureMap.lean`, part 4

The printed identity `N F_N^g = ½‖N^{-1/2} ∑ (Ψ(x_i) - μ(Ψ))‖² - ½ g(0)` for the feature map `Ψ` of
`O:eq:feature`, and for the negative-exponent kernel `O:sec:negative`: both are instances of
`energy_identity_of_feature_proof` (part 3), with the inner product identity `featureMap_inner_proof`
(part 2) and the spectral symbol `isSpectralSymbol_negSpectralCoeff_proof` (part 1).
-/

noncomputable section

open MeasureTheory

namespace HRS.MH.FeatureMap

open HRS

theorem energy_identity_featureMap_proof : type_of% @HRS.energy_identity_featureMap := by
  intro d a hsym μ _ N hN X
  exact energy_identity_of_feature_proof (StaticLimitAux.specKernel a)
    (featureMap hsym.nonneg hsym.summable) (continuous_featureMap_proof hsym)
    (featureMap_inner_proof hsym) μ hN X

/-- Stated with `isSpectralSymbol_negSpectralCoeff_proof` in place of the original witness: the two
witnesses are proofs of the same proposition, so this type is definitionally `type_of% @HRS.energy_identity_negSpectral`
(checked in the scratch file), but `type_of%` would mention the `sorry`-ed original and so put `sorryAx` into the axioms. -/
theorem energy_identity_negSpectral_proof {d : ℕ} {s c : ℝ} (hs : s < 0) (hc : 0 < c)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    (N : ℝ) * modulatedEnergyKernel (negSpectralKernel d s c) X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ •
          ∑ i, (featureMap (isSpectralSymbol_negSpectralCoeff_proof d hs hc).nonneg
                  (isSpectralSymbol_negSpectralCoeff_proof d hs hc).summable (X i) -
                ∫ y, featureMap (isSpectralSymbol_negSpectralCoeff_proof d hs hc).nonneg
                  (isSpectralSymbol_negSpectralCoeff_proof d hs hc).summable y ∂μ)‖ ^ 2
        - (1 / 2) * negSpectralKernel d s c 0 := by
  exact energy_identity_featureMap_proof (isSpectralSymbol_negSpectralCoeff_proof d hs hc) μ hN X

end HRS.MH.FeatureMap
