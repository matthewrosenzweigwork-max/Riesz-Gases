import HRS.MS.Fp81S21FutureIndep37

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2

/-- Extend the past path's all-time oscillator coordinates to arbitrary
oscillator tests, retaining their exact initial-and-past source features. -/
theorem fp81s21_past_path_all_test_eval (p : Parameters) :
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
      HRS.IsStdGaussianSeq P ξ → (∀ h, MemLp (W h) 2 P) →
      (∀ h, Tendsto (fun n : ℕ => ∫ ω,
        (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0)) →
      ∀ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H, Measurable X →
      (∀ t : Icc (0 : ℝ) H, ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
        OscDual.coord (OscPath.at' (X ω) t) α =
          W (J (WithLp.toLp 2
            (fp81s21_initialGaussianFeature p R hK t (oscTestFun (wholeSpaceIndex p.d : ℝ) α),
            movingNoiseFeature R 0 t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
              movingNoiseFeature R r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) ω) →
      ∀ (t : Icc (0 : ℝ) H) (φ : Euc p.d → ℝ),
        IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ᵐ ω ∂P,
        OscDual.eval (OscPath.at' (X ω) t) φ =
          W (J (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
            movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ))) ω := by
  obtain ⟨δa, hδa, hδahalf, ha⟩ := fp81s21_combinedFeature_horizon_bound p
  obtain ⟨δb, hδb, hδbhalf, hb⟩ := movingNoiseFeature_bounds p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδahalf, ?_⟩
  intro δ hδ hδle R hμ Mg K hK H hH r hr Ω mΩ P hP J e ξ W hParseval hstd hW2 hWlim X hXm hcoords t φ hφ
  have hδa' := hδle.trans (min_le_left δa δb)
  have hδb' := hδle.trans (min_le_right δa δb)
  have hhalf : δ ≤ 1 / 2 := hδa'.trans hδahalf
  obtain ⟨A, hA, hAbound⟩ := ha δ hδ hδa' R hμ H hH
  obtain ⟨B, hB, hBbound⟩ := (hb δ hδ hδb' R H hH).1 r hr t t.property
  let F : oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ] GaussianFeatureHilbert :=
    J.toLinearMap.comp (fp81s21_combinedFeatureLinear p R hδ hhalf hH hK t.property) -
      fp81s21_futureFeatureLinear p R hδ hhalf hH hr t.property J
  have hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ),
      ‖F ψ‖ ≤ C * oscNorm (wholeSpaceIndex p.d : ℝ) (ψ : Euc p.d → ℝ) := by
    refine ⟨A + B, add_nonneg hA hB, ?_⟩
    intro ψ
    change ‖J (fp81s21_combinedFeature p R hK t (ψ : Euc p.d → ℝ)) -
      fp81s21_futureFeatureLinear p R hδ hhalf hH hr t.property J ψ‖ ≤ _
    calc
      _ ≤ ‖J (fp81s21_combinedFeature p R hK t (ψ : Euc p.d → ℝ))‖ +
          ‖fp81s21_futureFeatureLinear p R hδ hhalf hH hr t.property J ψ‖ := norm_sub_le _ _
      _ ≤ A * oscNorm (wholeSpaceIndex p.d : ℝ) (ψ : Euc p.d → ℝ) +
          B * oscNorm (wholeSpaceIndex p.d : ℝ) (ψ : Euc p.d → ℝ) := by
        rw [J.norm_map, fp81s21_futureFeatureLinear_norm]
        exact add_le_add (hAbound Mg K hK t t.property _ ψ.property) (hBbound _ ψ.property)
      _ = _ := by ring
  have heq (ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ)) :
      F ψ = J (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t (ψ : Euc p.d → ℝ),
        movingNoiseFeature R 0 t (ψ : Euc p.d → ℝ) - movingNoiseFeature R r t (ψ : Euc p.d → ℝ))) := by
    change J (fp81s21_combinedFeature p R hK t (ψ : Euc p.d → ℝ)) -
      J (fp81s21_futureNoiseSourceFeature p R r t (ψ : Euc p.d → ℝ)) = _
    rw [← map_sub]
    congr 1
    apply WithLp.ofLp_injective
    simp [fp81s21_combinedFeature, fp81s21_futureNoiseSourceFeature]
  have hcoord : ∀ α : MultiIndex p.d,
      (fun ω => OscDual.coord (OscPath.at' (X ω) t) α) =ᵐ[P]
        W (F (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)) := by
    intro α
    filter_upwards [hcoords t] with ω hω
    simpa [heq, initialTestBasis] using hω α
  have hvm : Measurable (fun ω => OscPath.at' (X ω) t) :=
    (ContinuousMap.evalCLM ℝ t).continuous.measurable.comp hXm
  let φs : oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
  have heval := fp81s21_source_all_test_eval P e ξ W hParseval hstd hW2 hWlim
    (fun ω => OscPath.at' (X ω) t) hvm F hF hcoord φs
  filter_upwards [heval] with ω hω
  simpa only [heq] using hω

#print axioms fp81s21_past_path_all_test_eval
end HRS.Fp81.S21
end
