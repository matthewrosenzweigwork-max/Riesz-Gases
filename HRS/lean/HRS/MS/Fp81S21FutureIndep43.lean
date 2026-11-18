import HRS.MS.Fp81S21FutureIndep42
import HRS.MS.Fp81S21MovingHeat2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.S111X1

/-- One moving future family, realized on the retained source, satisfies the
heat derivative conditioning identity at every absolute right endpoint. -/
theorem fp81s21_retained_moving_heat_conditioning (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        (∀ H v, IsProbabilityMeasure (future H v)) ∧
        (∀ H : ℝ, 0 < H → ∀ r ∈ Icc (0 : ℝ) H,
          IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r (future H r)) ∧
        (∀ H : ℝ, 0 < H →
          ∀ (Φ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), MemCb 5 Φ →
          ∀ u : ℝ, ContDiff ℝ 5 (r2HeatFn (future H) Φ u) ∧
          ∀ j ≤ 5, ∀ y,
            iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y =
              ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(future H u) ∧
            ‖iteratedFDeriv ℝ j (r2HeatFn (future H) Φ u) y‖ ≤
              ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ∧
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
        ∃ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
          Measurable X ∧ P.map X = future H r ∧
          IndepFun (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
            W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) X P ∧
          (∀ (Y : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H), Measurable Y →
            Measurable[MeasurableSpace.comap
              (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
                W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] Y →
            ∀ (Φ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ), MemCb 5 Φ →
            ∀ (j : ℕ), j ≤ 5 → ∀ (h : Fin j → OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
            ∀ D : Ω → ℝ, Integrable D P →
            AEStronglyMeasurable[MeasurableSpace.comap
              (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
                W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] D P →
            Integrable (fun ω => D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h) P ∧
            Integrable (fun ω => D ω * iteratedFDeriv ℝ j (r2HeatFn (future H) Φ r) (Y ω) h) P ∧
            (∀ ω, iteratedFDeriv ℝ j (r2HeatFn (future H) Φ r) (Y ω) h =
              ∫ z, iteratedFDeriv ℝ j Φ (Y ω + z) h ∂(future H r)) ∧
            (∫ ω, D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h ∂P) =
              (∫ ω, D ω * iteratedFDeriv ℝ j (r2HeatFn (future H) Φ r) (Y ω) h ∂P) ∧
            ‖∫ ω, D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h ∂P‖ ≤
              ((⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) * ∏ i, ‖h i‖) * ∫ ω, ‖D ω‖ ∂P) := by
  obtain ⟨δa, ha, hahalf, hheat⟩ := fp81s21_moving_heat_regularity p
  obtain ⟨δb, hb, hbhalf, hsource⟩ := fp81s21_future_path_conditioning p
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hahalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨future, hprob, hgauss, hlip, hreg⟩ := hheat δ hδ (hδle.trans (min_le_left _ _)) R
  refine ⟨future, hprob, hgauss, (fun H hH => (hreg H hH).2.2.2.2), ?_⟩
  intro H hH r hr Ω mΩ P hP J e ξ W hparseval hstd hWm hW2 hWlim hcomb hcov
  letI : IsProbabilityMeasure (future H r) := hprob H r
  obtain ⟨X, hXm, hXlaw, heval, hind, hcond⟩ :=
    hsource δ hδ (hδle.trans (min_le_right _ _)) R H hH r hr P J e ξ W
      hparseval hstd hWm hW2 hWlim hcomb hcov (future H r) (hgauss H hH r hr)
  refine ⟨X, hXm, hXlaw, hind, ?_⟩
  intro Y hY hYpast Φ hΦ j hj h D hD hDpast
  obtain ⟨hi, hiheat, heq, hbound⟩ :=
    fp81s21_heat_derivative_conditioning P _ Y X hY hYpast hXm hind
      (future H) r hXlaw Φ hΦ j hj h D hD hDpast
  have hform := (fp81s21_heat_derivative_increment P (future H) r Φ hΦ j hj h Y hY D hD).1
  exact ⟨hi, hiheat, hform, heq, hbound⟩

#print axioms fp81s21_retained_moving_heat_conditioning
end HRS.Fp81.S21
end
