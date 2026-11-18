import HRS.MS.ProClosureS111PhysicalFeatureBounds
import HRS.MS.ProClosureS111FeatureEmbedding
import HRS.MS.ProClosureS111GaussianLaw

/-!
The actual shared-noise thermal Gaussian path pair. Both initial response
operators, their orthogonal Gaussian feature components, and the physical
common-noise feature are constructed from the thermal hypotheses. The
accepted Gaussian series and continuous modification then give the exact
frozen SharedThermalLaw on every original oscillator test.

There is no Gaussian-law, covariance-factorization, path-regularity,
orbit-input, or feature-bound premise. The preparation endpoint gamma=0
and observation endpoint t=0 are included in the same construction.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.S111T HRS.MS.R26T6

variable {d : ℕ}

/-- A genuine physical producer of the original shared thermal law.
The finite horizon is positive, as it is for every moving window `u+T`
in the frozen S11.1 relaxation statement. -/
theorem physical_shared_thermal_law (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hH : 0 < H)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho) :
    ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), IsProbabilityMeasure P ∧
      r26t6_SharedThermalLaw P s a beta gamma H rho
        (pairedProcess d (wholeSpaceIndex d) H hH.le) := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  obtain ⟨M0, c, S, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  let G0 : Fin 2 → ℝ → oscSub d (wholeSpaceIndex d) →ₗ[ℝ] PhysicalFeatureSpace mu :=
    physicalLinear hX hK hbeta.le hgamma
  obtain ⟨hF0, L, hL, hinc0⟩ :=
    physicalLinear_summed_bounds hX hK hbeta.le hgamma hd hs0 hs ha hbeta hrho H hH.le
  letI : SecondCountableTopology (Lp ℝ 2 mu) := inferInstance
  letI : SecondCountableTopology (NoiseHilbert mu) := inferInstance
  letI : SecondCountableTopology (WithLp 2 (Lp ℝ 2 mu × NoiseHilbert mu)) := inferInstance
  letI : SecondCountableTopology (Lp ℝ 2 mu × WithLp 2 (Lp ℝ 2 mu × NoiseHilbert mu)) := inferInstance
  letI : SecondCountableTopology (PhysicalFeatureSpace mu) := inferInstance
  obtain ⟨J⟩ := separable_feature_embedding (E := PhysicalFeatureSpace mu)
  let G : Fin 2 → ℝ → oscSub d (wholeSpaceIndex d) →ₗ[ℝ] GaussianFeatureHilbert :=
    fun i t => J.toLinearMap.comp (G0 i t)
  have hG : ∀ i, ∀ t ∈ Icc (0 : ℝ) H, ∃ B : ℝ, 0 ≤ B ∧
      ∀ phi : oscSub d (wholeSpaceIndex d),
        ‖G i t phi‖ ≤ B * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ) := by
    intro i t ht
    obtain ⟨B, hB, hbound⟩ :=
      physicalLinear_osc_bound hd hs0 hs ha hbeta hgamma hrho hX hK i ht.1
    refine ⟨B, hB, fun phi => ?_⟩
    change ‖J (G0 i t phi)‖ ≤ _
    rw [J.norm_map]
    exact hbound phi
  have hF : ∀ i, ∀ t ∈ Icc (0 : ℝ) H,
      Summable (fun alpha : MultiIndex d =>
        ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) := by
    intro i t ht
    change Summable (fun alpha : MultiIndex d =>
      ‖J (G0 i t (initialTestBasis (wholeSpaceIndex d) alpha))‖ ^ 2)
    simpa only [J.norm_map] using hF0 i t ht
  have hinc : ∀ i, ∀ t v : ℝ, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      Summable (fun alpha : MultiIndex d =>
        ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          G i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          G i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ≤ L * |t - v| := by
    intro i t v ht hv
    change Summable (fun alpha : MultiIndex d =>
      ‖J (G0 i t (initialTestBasis (wholeSpaceIndex d) alpha)) -
        J (G0 i v (initialTestBasis (wholeSpaceIndex d) alpha))‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖J (G0 i t (initialTestBasis (wholeSpaceIndex d) alpha)) -
          J (G0 i v (initialTestBasis (wholeSpaceIndex d) alpha))‖ ^ 2) ≤ L * |t - v|
    simpa only [← J.map_sub, J.norm_map] using hinc0 i t v ht hv
  have hGram : ∀ i j, ∀ t v : ℝ, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      ∀ phi psi : oscSub d (wholeSpaceIndex d),
      inner ℝ (G i t phi) (G j v psi) =
        (if i = j then HRS.Whole.susceptibilityCov (rieszKernel d s) mu
          (r26t6_preparation beta gamma i)
          (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t (phi : Euc d → ℝ))
          (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 v (psi : Euc d → ℝ))
        else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          t v (phi : Euc d → ℝ) (psi : Euc d → ℝ) := by
    intro i j t v ht hv phi psi
    change inner ℝ (J (G0 i t phi)) (J (G0 j v psi)) = _
    rw [J.inner_map_map]
    exact physicalLinear_gram hd hs0 hs ha hbeta hgamma hrho hX hK i j ht.1 hv.1 phi psi
  exact shared_thermal_law_of_linear_features d s a beta gamma H rho hH
    gaussianFeatureBasis G hG hF L hL hinc hGram

#print axioms physical_shared_thermal_law

end HRS.MS.ProClosureS111
