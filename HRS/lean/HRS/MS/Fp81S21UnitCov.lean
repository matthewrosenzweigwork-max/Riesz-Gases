import HRS.MS.CovMeasAux19

/-!
# S2.1(iii), packet 15d-3: generic unit-clock covariance properties

Exact Lean types introduced here:

```lean
fp81s21_UnitCovProps (K : Type) [NormedAddCommGroup K]
  [InnerProductSpace ℝ K] [CompleteSpace K] (C0 : ℝ)
  (Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
    VectorMeasure ℝ (ProjTensor2 (PathSp 1 K))) : Prop

fp81s21_unitCovProps_exists :
  ∃ C0 : ℝ, 0 ≤ C0 ∧
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
      [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
      [SecondCountableTopology K],
      ∃ Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
        VectorMeasure ℝ (ProjTensor2 (PathSp 1 K)),
        fp81s21_UnitCovProps K C0 Q
```

The constant is selected before the quantified Hilbert space. The five fields
are support, total variation, observations, cumulative continuity, and
linearity, matching `S101Jprops` at clock `1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- The five covariance-measure clauses at unit clock for an arbitrary real
Hilbert feature space. -/
structure fp81s21_UnitCovProps (K : Type) [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] (C0 : ℝ)
    (Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
      VectorMeasure ℝ (ProjTensor2 (PathSp 1 K))) : Prop where
  supp : ∀ D, IsTraceDensityL1 1 D → ∀ I, MeasurableSet I →
    Q D I = Q D (I ∩ Icc 0 1)
  tv : ∀ D, IsTraceDensityL1 1 D →
    (Q D).variation (Icc 0 1) ≤
      ENNReal.ofReal C0 * ∫⁻ r in Icc (0 : ℝ) 1, ENNReal.ofReal (traceNormForm (D r))
  obs : ∀ D, IsTraceDensityL1 1 D →
    ∀ (t₁ t₂ : Icc (0 : ℝ) 1) (ℓ₁ ℓ₂ : K →L[ℝ] ℝ) (I : Set ℝ),
      MeasurableSet I →
      tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (Q D I) =
        ∫ r in I ∩ Icc 0 (min (t₁ : ℝ) t₂),
          D r (pullbackVec (s56_idEvol K) t₁ r ℓ₁)
            (pullbackVec (s56_idEvol K) t₂ r ℓ₂)
  cont : ∀ D, IsTraceDensityL1 1 D →
    ContinuousOn (fun t => Q D (Icc 0 t)) (Icc 0 1)
  lin : ∀ D D', IsTraceDensityL1 1 D → IsTraceDensityL1 1 D' →
    ∀ a b : ℝ, ∀ I, MeasurableSet I →
      Q (fun r => a • D r + b • D' r) I = a • Q D I + b • Q D' I

/-- The covariance theorem supplies one constant uniformly before every
eligible Hilbert feature space, by specializing its clock and evolution to
`1` and the identity evolution. -/
theorem fp81s21_unitCovProps_exists :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
        [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
        [SecondCountableTopology K],
        ∃ Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
          VectorMeasure ℝ (ProjTensor2 (PathSp 1 K)),
          fp81s21_UnitCovProps K C0 Q := by
  obtain ⟨C0, hC0, hC⟩ := HRS.Uniform.covariance_measure_proof 1 1 (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  intro K instNorm instInner instComplete instMeas instBorel instSecond
  obtain ⟨Q, hQ⟩ := hC K K (s56_idEvol K) (s56_idEvol_maxHyp (K := K) 1)
  refine ⟨Q, ?_⟩
  rcases hQ with ⟨hmain, hlin⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D hD I hI
    exact (hmain D hD).1 I hI
  · intro D hD
    exact (hmain D hD).2.2.1
  · intro D hD t₁ t₂ ℓ₁ ℓ₂ I hI
    exact (hmain D hD).2.2.2.1 t₁ t₂ ℓ₁ ℓ₂ I hI
  · intro D hD
    exact (hmain D hD).2.2.2.2
  · intro D D' hD hD' a b I hI
    exact hlin D D' hD hD' a b I hI

#print axioms fp81s21_unitCovProps_exists

end HRS.Fp81.S21

end
