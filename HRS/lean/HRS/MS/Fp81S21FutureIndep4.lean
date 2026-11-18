import HRS.MS.Fp81S21NoiseTails2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.ProClosureS111
open HRS.MS.R26T3
open HRS.MS.S111X2

/-- A retained isonormal source exposing Gaussian linear-combination laws and
covariances for all vectors in the initial/noise feature space. -/
theorem fp81s21_future_common_source
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg) :
    ∃ (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (hP : IsProbabilityMeasure P)
      (e : ℕ → GaussianFeatureHilbert)
      (ξ : ℕ → Ω → ℝ) (W : GaussianFeatureHilbert → Ω → ℝ),
      (∀ h h' : GaussianFeatureHilbert,
        HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h')) ∧
      HRS.IsStdGaussianSeq P ξ ∧
      (∀ h, Measurable (W h)) ∧
      (∀ h, MemLp (W h) 2 P) ∧
      (∀ h, Tendsto (fun m : ℕ =>
        ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
        P.map (fun ω => ∑ i, c i * W (f i) ω) =
          gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))) ∧
      (∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h') ∧
      (∀ r t : ℝ, 0 ≤ r → 0 ≤ t →
        ∀ ψ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∫ ω, W (J (@fp81s21_combinedFeature p δ R hμ₀ Mg K hK r ψ)) ω *
              W (J (@fp81s21_combinedFeature p δ R hμ₀ Mg K hK t φ)) ω ∂P =
            HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  letI : SecondCountableTopology (Lp ℝ 2 (r26t3_mu R 0)) := inferInstance
  letI : SecondCountableTopology (MovingNoiseHilbert p.d) := inferInstance
  letI : SecondCountableTopology (Fp81S21GaussFeatureHilbert p R) := inferInstance
  obtain ⟨J⟩ := separable_feature_embedding (E := Fp81S21GaussFeatureHilbert p R)
  obtain ⟨e, he⟩ := s21g2_s11a_parseval GaussianFeatureHilbert
  obtain ⟨Ω, mΩ, P, hP, ξ, W, hstd, -, hWm, hW2, hWlim, hcomb, hcov⟩ :=
    s21g2_s11a_isonormal e he
  refine ⟨J, Ω, mΩ, P, hP, e, ξ, W, he, hstd, hWm, hW2, hWlim,
    hcomb, hcov, ?_⟩
  intro r t hr ht ψ φ hψ hφ
  calc
    _ = inner ℝ (J (fp81s21_combinedFeature p R hK r ψ))
          (J (fp81s21_combinedFeature p R hK t φ)) := hcov _ _
    _ = inner ℝ (fp81s21_combinedFeature p R hK r ψ)
          (fp81s21_combinedFeature p R hK t φ) := J.inner_map_map _ _
    _ = HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ :=
      fp81s21_combinedFeature_gram p hδ hδhalf R hK hr ht hψ hφ

#print axioms fp81s21_future_common_source

end HRS.Fp81.S21
end
