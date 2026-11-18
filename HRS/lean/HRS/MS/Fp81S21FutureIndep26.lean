import HRS.MS.Fp81S21FutureIndep25

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.S111X1

/-- A retained-source future path with its exact law, test evaluations,
independence, and conditional factorization against all integrable past increments. -/
theorem fp81s21_future_path_conditioning (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H → ∀ r ∈ Icc (0 : ℝ) H,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
      (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
      (W : GaussianFeatureHilbert → Ω → ℝ),
      (∀ h h', HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h')) →
      HRS.IsStdGaussianSeq P ξ →
      (∀ h, Measurable (W h)) → (∀ h, MemLp (W h) 2 P) →
      (∀ h, Tendsto (fun n : ℕ => ∫ ω,
        (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0)) →
      (∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
        P.map (fun ω => ∑ i, c i * W (f i) ω) =
          gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))) →
      (∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h') →
      ∀ (γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
        [IsProbabilityMeasure γ],
      IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r γ →
      ∃ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
        Measurable X ∧ P.map X = γ ∧
        (∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
          OscDual.eval (OscPath.at' (X ω) t) φ =
            W (J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω) ∧
        IndepFun (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) X P ∧
        (∀ (f : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), Measurable f →
          ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) → ∀ D : Ω → ℝ, Integrable D P →
          AEStronglyMeasurable[MeasurableSpace.comap
            (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
              W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] D P →
          Integrable (fun ω => D ω * f (X ω)) P ∧
          P[fun ω => D ω * f (X ω) | MeasurableSpace.comap
            (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
              W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] =ᵐ[P]
            fun ω => D ω * ∫ z, f z ∂γ) := by
  obtain ⟨δ0, hδ0, hδhalf, hpath⟩ := fp81s21_future_path_all_test_eval p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R H hH r hr Ω mΩ P hP J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov γ hγp hγ
  obtain ⟨X, hXm, hXlaw, heval, hind⟩ :=
    hpath δ hδ hδle R H hH r hr P J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov γ hγ
  refine ⟨X, hXm, hXlaw, heval, hind, ?_⟩
  intro f hf C hC D hD hDpast
  exact fp81s21_independent_future_conditional P _ X
    (measurable_pi_iff.2 fun _ => hWm _) hXm hind γ hXlaw f hf C hC D hD hDpast

#print axioms fp81s21_future_path_conditioning
end HRS.Fp81.S21
end
