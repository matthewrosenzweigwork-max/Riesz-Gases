import HRS.MS.Fp81S21GaussianPredictionDecomposition

/-! Packet 36B, part (ii), producer. The radius precedes the supplied Physical35
package. FutureIndep39 is applied to its retained source and a supplied compatible
future law; its selected paths and feature evaluations are kept together.
The prediction/past identification, part (i), is not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

local instance fp81s21_decomposition2_initial_probability :
    IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R

/-- A coherent FutureIndep39 selection on the supplied package's source.
The initial, past and future paths are not selected independently. -/
structure fp81s21_RetainedCutoffPaths (Q : fp81s21_Physical35 p R) (a r : ℝ)
    (γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))) where
  X0 : Q.src.G0.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)
  Xpast : Q.src.G0.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)
  Xfuture : Q.src.G0.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)
  measurable_zero : Measurable X0
  measurable_past : Measurable Xpast
  measurable_future : Measurable Xfuture
  zero_law : Q.src.G0.P.map X0 = Q.src.G0.P.map
    (processWindow (wholeSpaceIndex p.d : ℝ) (a + p.T) 0 Q.src.G0.Z)
  future_law : Q.src.G0.P.map Xfuture = γ
  sum : ∀ᵐ ω ∂Q.src.G0.P, X0 ω = Xpast ω + Xfuture ω
  past_measurable : Measurable[MeasurableSpace.comap
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection r) inferInstance] Xpast
  independent_paths : IndepFun Xpast Xfuture Q.src.G0.P
  independent_past : IndepFun
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection r) Xfuture Q.src.G0.P
  evaluations : fp81s21_CutoffSourceEvaluations Q (a + p.T) r Xpast Xfuture
  propagated : ∀ (t : Icc (0 : ℝ) (a + p.T)), r ≤ t → ∀ φ : Euc p.d → ℝ,
    IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂Q.src.G0.P,
      OscDual.eval (OscPath.at' (Xpast ω) t) φ =
        Q.src.W (Q.src.J (fp81s21_combinedFeature p R Q.src.hK r
          (propagatorW (r26t3_coeff R) r t φ))) ω

/-- The supplied retained source admits the FutureIndep39 cutoff selection
whose past-plus-future window is the actual retained Z window, samplewise a.e.
This is part (ii), not the still separate identification with the 36A prediction. -/
theorem fp81s21_gaussian_cutoff_source_decomposition (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∀ r ∈ Icc (0 : ℝ) (a + p.T),
      ∀ γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)),
      ∀ [IsProbabilityMeasure γ],
      IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T) r γ →
      ∃ D : fp81s21_RetainedCutoffPaths Q a r γ,
        (fun ω => physicalWindowRestriction ha (le_refl (a + p.T))
          (D.Xpast ω + D.Xfuture ω)) =ᵐ[Q.src.G0.P] r26t3_Zpath Q.src.G0 a := by
  obtain ⟨δ₀, hδ₀, hhalf, hcut⟩ := fp81s21_retained_gaussian_past_future p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q a ha r hr γ hγprob hγ
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  obtain ⟨X0, Xp, Xf, h0m, hpm, hfm, h0law, hflaw, hsum, hpast,
    _, _, heval, hprop, hind, hfuture, hindPast, _⟩ :=
    hcut δ hδ hδle R Q.src.Mg Q.src.K Q.src.hK (a + p.T) hH r hr
      Q.src.G0.P Q.src.J Q.src.e Q.src.ξ Q.src.W
      Q.src.rawBundle.2.1 Q.src.rawBundle.2.2.1 Q.src.rawBundle.2.2.2.1
      Q.src.rawBundle.2.2.2.2.1 Q.src.rawBundle.2.2.2.2.2.1
      Q.src.allFeatureGaussianLaw Q.src.allFeatureCovariance Q.src.G0 γ hγ
  let D : fp81s21_RetainedCutoffPaths Q a r γ := {
    X0 := X0, Xpast := Xp, Xfuture := Xf
    measurable_zero := h0m, measurable_past := hpm, measurable_future := hfm
    zero_law := h0law, future_law := hflaw, sum := hsum
    past_measurable := hpast, independent_paths := hind, independent_past := hindPast
    evaluations := ⟨heval, hfuture⟩, propagated := hprop }
  exact ⟨D, fp81s21_source_cutoff_window_sum Q a ha r Xp Xf D.evaluations⟩

#print axioms fp81s21_gaussian_cutoff_source_decomposition
end HRS.Fp81.S21
end
