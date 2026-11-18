import HRS.MS.Fp81S21FutureIndep20

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath

/-- The independent future path agrees with the retained source at every fixed
terminal time and simultaneously in all countably many oscillator coordinates. -/
theorem fp81s21_future_path_all_time_coordinates (p : Parameters) :
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
        (∀ t : Icc (0 : ℝ) H, ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
          OscDual.coord (OscPath.at' (X ω) t) α =
            W (J (fp81s21_futureNoiseSourceFeature p R r t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ∧
        IndepFun (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) X P := by
  obtain ⟨δ0, hδ0, hδhalf, hF⟩ := fp81s21_future_coordinate_feature_continuous p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R H hH r hr Ω mΩ P hP J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov γ hγp hγ
  obtain ⟨X, hXm, hXlaw, ⟨s, hs, hcoord⟩, hind⟩ :=
    fp81s21_future_path_independent_of_past_source p R hδ (hδle.trans hδhalf)
      hH hr P J W hWm hW2 hcomb hcov γ hγ
  refine ⟨X, hXm, hXlaw, ?_, hind⟩
  intro t
  apply ae_all_iff.2
  intro α
  let F : Icc (0 : ℝ) H → GaussianFeatureHilbert := fun u =>
    J (fp81s21_futureNoiseSourceFeature p R r u
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
  have hFc : Continuous F := J.continuous.comp (hF δ hδ hδle R H hH r hr α)
  have hc : ∀ n, (fun ω => OscDual.coord (OscPath.at' (X ω) (s n)) α) =ᵐ[P] W (F (s n)) := by
    intro n
    filter_upwards [hcoord] with ω hω
    exact hω (n, α)
  exact fp81s21_source_coordinate_at_every_time P e ξ W hParseval hstd hW2 hWlim X hXm s hs F hFc α hc t

#print axioms fp81s21_future_path_all_time_coordinates
end HRS.Fp81.S21
end
