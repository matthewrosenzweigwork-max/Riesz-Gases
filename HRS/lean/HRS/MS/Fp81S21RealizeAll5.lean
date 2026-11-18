import HRS.MS.Fp81S21RealizeAll4
import HRS.MS.Fp81S21GaussFeature
import HRS.MS.S21F_D01

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- For every sufficiently small δ and every trajectory, the retained raw
Gaussian family admits a continuous path modification on its original space. -/
theorem fp81s21_gaussianRealization_nonempty (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ R : Trajectory p δ, Nonempty (GaussianRealization R) := by
  obtain ⟨δ0, hδ0, hδ0half, hretained⟩ :=
    fp81s21_realize_retained_bundle p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hμ₀ : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  rcases hretained δ hδ hδle R hμ₀ with
    ⟨Mg, K, hK, V, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
      hBundle0, hNorm, hFeatureBound⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  rcases hBundle0 with
    ⟨hTrace, hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZ2, hcoord, hZsecond⟩
  let hBundle : fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0 :=
    ⟨hTrace, hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZ2, hcoord, hZsecond⟩
  have _hRawEval : ∀ t : ℝ, 0 ≤ t → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      (fun ω => OscDual.eval (Z0 t ω) φ) =ᵐ[P]
        fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω := by
    intro t ht φ hφ
    exact fp81s21_raw_eval p hδ hδhalf R hμ₀ hK J e ξ W Z0
      hParseval hstd hW2 hWlim hZ2 hcoord hFeatureBound t ht φ hφ
  have _hRawEvalBundle : ∀ t : ℝ, 0 ≤ t → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      (fun ω => OscDual.eval (Z0 t ω) φ) =ᵐ[P]
        fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω := by
    intro t ht φ hφ
    exact fp81s21_raw_eval_bundle p hδ hδhalf R hμ₀ hK V J e ξ W Z0
      hBundle hFeatureBound t ht φ hφ
  have hLocal := fp81s21_realize_local_modifications Z0 hZmeas hNorm
  rcases hLocal with ⟨Y, hYmeas, hYmod⟩
  obtain ⟨Z, hZjoint, hZcont, hmod⟩ :=
    fp81s21_realize_patched_process Z0 Y hYmeas hYmod
  have hZmeas' : ∀ t, Measurable (Z t) := by
    intro t
    have hslice : Measurable (fun ω : Ω => (t, ω)) := measurable_prodMk_left
    exact hZjoint.comp hslice
  have hRawLaw : ∀ (n : ℕ) (τ : Fin n → ℝ)
      (φ : Fin n → Euc p.d → ℝ),
      (∀ i, 0 ≤ τ i) →
      (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
      HRS.law P (fun ω => (WithLp.toLp 2 fun i =>
        OscDual.eval (Z0 (τ i) ω) (φ i) :
          EuclideanSpace ℝ (Fin n))) =
        ProbabilityTheory.multivariateGaussian 0
          (fp81s21_rawJointCovariance p R τ φ) := by
    intro n τ φ hτ hφ
    exact (fp81s21_raw_joint_law p hδ hδhalf R hμ₀ hK V
      J e ξ W Z0 hBundle hFeatureBound n τ φ hτ hφ).2
  have hEvolution := fp81s21_realize_evolution_all_horizons R Z Z0
    hZmeas' hZcont hmod hRawLaw
  exact ⟨⟨Ω, P, Z, hEvolution⟩⟩

#print axioms fp81s21_gaussianRealization_nonempty

end HRS.Fp81.S21

end
