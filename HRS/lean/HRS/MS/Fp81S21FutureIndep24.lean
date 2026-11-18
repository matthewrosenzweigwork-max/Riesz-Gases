import HRS.MS.Fp81S21FutureIndep23

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.S111X1

/-- The independent future path evaluates every oscillator test as its
retained future-source feature, for each fixed time and test. -/
theorem fp81s21_future_path_all_test_eval (p : Parameters) :
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
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) X P := by
  obtain ⟨δa, hδa, hδahalf, ha⟩ := fp81s21_future_path_all_time_coordinates p
  obtain ⟨δb, hδb, hδbhalf, hb⟩ := movingNoiseFeature_bounds p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδahalf, ?_⟩
  intro δ hδ hδle R H hH r hr Ω mΩ P hP J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov γ hγp hγ
  have hδa' : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hδb' : δ ≤ δb := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδa'.trans hδahalf
  obtain ⟨X, hXm, hXlaw, hcoord, hind⟩ :=
    ha δ hδ hδa' R H hH r hr P J e ξ W hParseval hstd hWm hW2 hWlim hcomb hcov γ hγ
  refine ⟨X, hXm, hXlaw, ?_, hind⟩
  intro t φ hφ
  let φs : oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
  let F := fp81s21_futureFeatureLinear p R hδ hδhalf hH hr t.property J
  obtain ⟨B, hB, hbound⟩ := (hb δ hδ hδb' R H hH).1 r hr t t.property
  have hF : ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ),
      ‖F ψ‖ ≤ B * oscNorm (wholeSpaceIndex p.d : ℝ) (ψ : Euc p.d → ℝ) := by
    refine ⟨B, hB, ?_⟩
    intro ψ
    rw [fp81s21_futureFeatureLinear_norm]
    exact hbound _ ψ.property
  have hvm : Measurable (fun ω => OscPath.at' (X ω) t) :=
    (ContinuousMap.evalCLM ℝ t).continuous.measurable.comp hXm
  have hc : ∀ α : MultiIndex p.d,
      (fun ω => OscDual.coord (OscPath.at' (X ω) t) α) =ᵐ[P]
        W (F (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)) := by
    intro α
    filter_upwards [hcoord t] with ω hω
    simpa [F, fp81s21_futureFeatureLinear, initialTestBasis] using hω α
  have heval := fp81s21_source_all_test_eval P e ξ W hParseval hstd hW2 hWlim
      (fun ω => OscPath.at' (X ω) t) hvm F hF hc φs
  filter_upwards [heval] with ω hω
  exact hω

#print axioms fp81s21_future_path_all_test_eval
end HRS.Fp81.S21
end
