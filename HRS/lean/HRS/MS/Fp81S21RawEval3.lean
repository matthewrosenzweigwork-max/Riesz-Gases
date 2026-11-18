import HRS.MS.Fp81S21RawEval2
import HRS.MS.Fp81S21GaussFeature2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2

/-- The packaged raw Gaussian family can be chosen so its raw oscillator
family agrees with its Gaussian feature evaluation for every fixed time and
test, and its finite vectors have the exact physical Gaussian law. -/
theorem fp81s21_rawGaussianFamily_allTests (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
          Lp ℝ 2 (r26t3_mu R 0),
        ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
        ∃ V : ℝ,
        ∃ J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert,
        ∃ Ω : Type, ∃ mΩ : MeasurableSpace Ω, ∃ P : Measure Ω,
        ∃ hP : IsProbabilityMeasure P,
        ∃ e : ℕ → GaussianFeatureHilbert, ∃ ξ : ℕ → Ω → ℝ,
        ∃ W : GaussianFeatureHilbert → Ω → ℝ,
        ∃ Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ),
          fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0 ∧
          (∀ t : ℝ, 0 ≤ t → ∀ φ : Euc p.d → ℝ,
            IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
            (fun ω => OscDual.eval (Z0 t ω) φ) =ᵐ[P]
              fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω) ∧
          (∀ n : ℕ, ∀ τ : Fin n → ℝ, ∀ φ : Fin n → Euc p.d → ℝ,
            (∀ i, 0 ≤ τ i) →
            (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
            (fp81s21_rawJointCovariance p R τ φ).PosSemidef ∧
              HRS.law P (fun ω => (WithLp.toLp 2 fun i =>
                OscDual.eval (Z0 (τ i) ω) (φ i) :
                  EuclideanSpace ℝ (Fin n))) =
                ProbabilityTheory.multivariateGaussian 0
                  (fp81s21_rawJointCovariance p R τ φ)) := by
  obtain ⟨δR, hδR, hδRhalf, hRaw⟩ := fp81s21_rawGaussianFamily p
  obtain ⟨δH, hδH, hδHhalf, hHorizon⟩ :=
    fp81s21_combinedFeature_horizon_bound p
  let δ0 : ℝ := min δR δH
  have hδ0 : 0 < δ0 := lt_min hδR hδH
  have hδ0half : δ0 ≤ 1 / 2 :=
    le_trans (min_le_left _ _) hδRhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hμ₀
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hδRle : δ ≤ δR := hδle.trans (min_le_left _ _)
  have hδHle : δ ≤ δH := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  obtain ⟨Mg, K, hK, V, hTrace, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
      hParseval, hstd, hWm, hW2, hWlim, hCov, hJoint,
      hZmeas, hZ2, hcoord, hNorm⟩ := hRaw δ hδ hδRle R
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hBundle : fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0 :=
    ⟨hTrace, hParseval, hstd, hWm, hW2, hWlim, hCov, hJoint,
      hZmeas, hZ2, hcoord, hNorm⟩
  have hFeatureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ := by
    intro t ht
    let H : ℝ := t + 1
    have hH : 0 < H := by dsimp [H]; linarith
    obtain ⟨B, hB, hBound⟩ := hHorizon δ hδ hδHle R hμ₀ H hH
    refine ⟨B, hB, ?_⟩
    intro ψ hψ
    exact hBound Mg K hK t ⟨ht, by dsimp [H]; linarith⟩ ψ hψ
  refine ⟨Mg, K, hK, V, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
    hBundle, ?_, ?_⟩
  · intro t ht φ hφ
    exact fp81s21_raw_eval_bundle p hδ hδhalf R hμ₀ hK V J e ξ W Z0
      hBundle hFeatureBound t ht φ hφ
  · intro n τ φ hτ hφ
    exact fp81s21_raw_joint_law p hδ hδhalf R hμ₀ hK V J e ξ W Z0
      hBundle hFeatureBound n τ φ hτ hφ

#print axioms fp81s21_rawGaussianFamily_allTests

end HRS.Fp81.S21

end
