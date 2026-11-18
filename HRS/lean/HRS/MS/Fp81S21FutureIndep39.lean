import HRS.MS.Fp81S21FutureIndep38

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.R2Interp HRS.MS.S111X2

/-- Retained-source full Gaussian decomposition, oscillator-test identity,
path independence and conditioning at the absolute cutoff. -/
theorem fp81s21_retained_gaussian_past_future (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ [IsProbabilityMeasure (r26t3_mu R 0)]
      (Mg : ℝ) (K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0))
      (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg),
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
      ∀ (G : GaussianRealization R) (γr : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
        [IsProbabilityMeasure γr],
      IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r γr →
      ∃ X0 Xpast Xfuture : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
        Measurable X0 ∧ Measurable Xpast ∧ Measurable Xfuture ∧
        P.map X0 = G.P.map (processWindow (wholeSpaceIndex p.d : ℝ) H 0 G.Z) ∧ P.map Xfuture = γr ∧
        (∀ᵐ ω ∂P, X0 ω = Xpast ω + Xfuture ω) ∧
        Measurable[MeasurableSpace.comap
          (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
            W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] Xpast ∧
        (∃ s : ℕ → Icc (0 : ℝ) H, DenseRange s ∧
          ∀ᵐ ω ∂P, ∀ i : ℕ × MultiIndex p.d,
            OscDual.coord (OscPath.at' (Xpast ω) (s i.1)) i.2 =
              W (J (WithLp.toLp 2
                (fp81s21_initialGaussianFeature p R hK (s i.1)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2),
                movingNoiseFeature R 0 (s i.1) (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2) -
                  movingNoiseFeature R r (s i.1) (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2)))) ω) ∧
        (∀ t : Icc (0 : ℝ) H, ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
          OscDual.coord (OscPath.at' (Xpast ω) t) α =
            W (J (WithLp.toLp 2
              (fp81s21_initialGaussianFeature p R hK t (oscTestFun (wholeSpaceIndex p.d : ℝ) α),
              movingNoiseFeature R 0 t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
                movingNoiseFeature R r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) ω) ∧
        (∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
          OscDual.eval (OscPath.at' (Xpast ω) t) φ =
            W (J (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
              movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ))) ω) ∧
        (∀ (t : Icc (0 : ℝ) H), r ≤ t → ∀ (φ : Euc p.d → ℝ),
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
          OscDual.eval (OscPath.at' (Xpast ω) t) φ =
            W (J (fp81s21_combinedFeature p R hK r (propagatorW (r26t3_coeff R) r t φ))) ω) ∧
        IndepFun Xpast Xfuture P ∧
        (∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
          OscDual.eval (OscPath.at' (Xfuture ω) t) φ =
            W (J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω) ∧
        IndepFun (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) Xfuture P ∧
        (∀ (f : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), Measurable f →
          ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) → ∀ D : Ω → ℝ, Integrable D P →
          AEStronglyMeasurable[MeasurableSpace.comap
            (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
              W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] D P →
          Integrable (fun ω => D ω * f (Xfuture ω)) P ∧
          P[fun ω => D ω * f (Xfuture ω) | MeasurableSpace.comap
            (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
              W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] =ᵐ[P]
            fun ω => D ω * ∫ z, f z ∂γr) := by
  obtain ⟨δa, hδa, hδahalf, ha⟩ := fp81s21_retained_gaussian_decomposition_all_times p
  obtain ⟨δb, hδb, hδbhalf, hb⟩ := fp81s21_past_path_all_test_eval p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδahalf, ?_⟩
  intro δ hδ hδle R hμ Mg K hK H hH r hr Ω mΩ P hP J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov G γr hγrp hγr
  have hδa' := hδle.trans (min_le_left δa δb)
  have hδb' := hδle.trans (min_le_right δa δb)
  have hhalf := hδa'.trans hδahalf
  obtain ⟨X0, Xp, Xr, hX0m, hXpm, hXrm, hX0law, hXrlaw, hsum, hXpPast,
    hdense, hcoords, hind, heval, hindPast, hcond⟩ :=
    ha δ hδ hδa' R Mg K hK H hH r hr P J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov G γr hγr
  have hpast := hb δ hδ hδb' R Mg K hK H hH r hr P J e ξ W hParseval hstd hW2 hWlim Xp hXpm hcoords
  have hprop : ∀ (t : Icc (0 : ℝ) H), r ≤ t → ∀ (φ : Euc p.d → ℝ),
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
      OscDual.eval (OscPath.at' (Xp ω) t) φ =
        W (J (fp81s21_combinedFeature p R hK r (propagatorW (r26t3_coeff R) r t φ))) ω := by
    intro t hrt φ hφ
    filter_upwards [hpast t φ hφ] with ω hω
    rw [fp81s21_propagated_combined_feature p R hδ hhalf hH hK hr t.property hrt hφ]
    exact hω
  exact ⟨X0, Xp, Xr, hX0m, hXpm, hXrm, hX0law, hXrlaw, hsum, hXpPast,
    hdense, hcoords, hpast, hprop, hind, heval, hindPast, hcond⟩

#print axioms fp81s21_retained_gaussian_past_future
end HRS.Fp81.S21
end
