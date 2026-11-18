import HRS.MS.Fp81S21RawGauss4
import HRS.MS.ProClosureS111GaussianLaw

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.MovOsc HRS.MS.S111X1 HRS.MS.S111X2

private theorem fp81s21_raw_eval_test_sub {d : ℕ} {m : ℝ}
    (z : OscDual d m) (ψ χ : oscSub d m) :
    OscDual.eval z (ψ : Euc d → ℝ) - OscDual.eval z (χ : Euc d → ℝ) =
      OscDual.eval z ((ψ - χ : oscSub d m) : Euc d → ℝ) := by
  rw [← OscDual.toDual_ofFun z _ ψ.property.2,
    ← OscDual.toDual_ofFun z _ χ.property.2, ← map_sub,
    ← initialTest_ofFun_sub ψ χ, OscDual.toDual_ofFun z _ (ψ - χ).property.2]

private theorem fp81s21_raw_eval_section_tail_norm {d : ℕ} {m : ℝ}
    (φ : oscSub d m) :
    Tendsto (fun n => oscNorm m
      ((initialTestSection φ n - φ : oscSub d m) : Euc d → ℝ)) atTop (𝓝 0) := by
  have htail := initialTestSection_tail φ
  have heq : ∀ n, oscNorm m
      ((initialTestSection φ n - φ : oscSub d m) : Euc d → ℝ) =
      oscNorm m ((φ - initialTestSection φ n : oscSub d m) : Euc d → ℝ) := by
    intro n
    calc
      _ = ‖OscSpace.ofFun m
          ((initialTestSection φ n - φ : oscSub d m) : Euc d → ℝ)‖ :=
        (OscSpace.norm_ofFun _ (initialTestSection φ n - φ).property.2).symm
      _ = ‖OscSpace.ofFun m (initialTestSection φ n : Euc d → ℝ) -
          OscSpace.ofFun m (φ : Euc d → ℝ)‖ := by rw [initialTest_ofFun_sub]
      _ = ‖OscSpace.ofFun m (φ : Euc d → ℝ) -
          OscSpace.ofFun m (initialTestSection φ n : Euc d → ℝ)‖ := norm_sub_rev _ _
      _ = _ := by
        rw [← initialTest_ofFun_sub φ (initialTestSection φ n)]
        exact OscSpace.norm_ofFun _ (φ - initialTestSection φ n).property.2
  exact htail.congr fun n => (heq n).symm

private theorem fp81s21_raw_W_finset_linear
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : G → Ω → ℝ)
    (hlinear : ∀ u v c, W (u + c • v) =ᵐ[P] fun ω => W u ω + c * W v ω)
    (f : ι → G) (c : ι → ℝ) (S : Finset ι) :
    W (∑ i ∈ S, c i • f i) =ᵐ[P] fun ω => ∑ i ∈ S, c i * W (f i) ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 := hlinear (0 : G) 0 1
      filter_upwards [h0] with ω hω
      have hz : W (0 : G) ω = 0 := by
        simp only [add_zero, one_smul] at hω
        linarith
      simpa using hz
  | @insert a S ha ih =>
      have hs := hlinear (∑ i ∈ S, c i • f i) (f a) (c a)
      filter_upwards [hs, ih] with ω hω hS
      rw [Finset.sum_insert ha]
      have hω' : W (c a • f a + ∑ i ∈ S, c i • f i) ω =
          W (∑ i ∈ S, c i • f i) ω + c a * W (f a) ω := by
        simpa [add_comm, add_left_comm, add_assoc] using hω
      rw [hω', hS]
      simp only [Finset.sum_insert ha]
      ring

/-- All-test evaluation of the raw oscillator family, from the common-series
bundle. The feature envelope is stated for the fixed time; the packaged
corollary below obtains it from the uniform finite-horizon bound. -/
theorem fp81s21_raw_eval
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ))
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (hZ2 : ∀ t, MemLp (Z0 t) 2 P)
    (hcoord : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
      OscDual.coord (Z0 t ω) α = W (J (fp81s21_combinedFeature p R hK t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω)
    (hFeatureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ)
    (t : ℝ) (ht : 0 ≤ t) (φ : Euc p.d → ℝ)
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    (fun ω => OscDual.eval (Z0 t ω) φ) =ᵐ[P]
      fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  let m : ℝ := wholeSpaceIndex p.d
  let φs : oscSub p.d m := ⟨φ, hφ⟩
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t ∈ Set.Icc (0 : ℝ) H := by
    constructor
    · exact ht
    · dsimp [H]; linarith
  have hfeatureZero : fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) = 0 := by
    have hz := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK htH
      (ψ := (0 : Euc p.d → ℝ)) (φ := (0 : Euc p.d → ℝ))
      (HRS.MS.S111X1.oscSub p.d m).zero_mem
      (HRS.MS.S111X1.oscSub p.d m).zero_mem 1
    have hfun : (fun x : Euc p.d => (0 : Euc p.d → ℝ) x +
        1 * (0 : Euc p.d → ℝ) x) = (0 : Euc p.d → ℝ) := by
      funext x
      simp
    have hfeatureFun := congrArg
      (fun f : Euc p.d → ℝ => fp81s21_combinedFeature p R hK t f) hfun
    have hz' : fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) =
        fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) +
          fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) := by
      calc
        _ = fp81s21_combinedFeature p R hK t
            (fun x : Euc p.d => (0 : Euc p.d → ℝ) x +
              1 * (0 : Euc p.d → ℝ) x) := hfeatureFun.symm
        _ = _ := by simpa using hz
    have hz'' : fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) + 0 =
        fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) +
          fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) := by
      simpa using hz'
    exact (add_left_cancel hz'').symm
  let F : oscSub p.d m →ₗ[ℝ] Fp81S21GaussFeatureHilbert p R :=
    { toFun := fun ψ => fp81s21_combinedFeature p R hK t (ψ : Euc p.d → ℝ)
      map_add' := by
        intro ψ χ
        have hadd := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK htH
          ψ.property χ.property 1
        change fp81s21_combinedFeature p R hK t
          (fun x => (ψ : Euc p.d → ℝ) x + (χ : Euc p.d → ℝ) x) = _
        simpa [one_mul] using hadd
      map_smul' := by
        intro c ψ
        have hsmul := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK htH
          (HRS.MS.S111X1.oscSub p.d m).zero_mem ψ.property c
        change fp81s21_combinedFeature p R hK t
          (fun x => c * (ψ : Euc p.d → ℝ) x) = _
        simpa [hfeatureZero, smul_eq_mul] using hsmul }
  obtain ⟨B, hB, hFB⟩ := hFeatureBound t ht
  have hFbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : oscSub p.d m,
      ‖F ψ‖ ≤ B * oscNorm m (ψ : Euc p.d → ℝ) := by
    refine ⟨B, hB, ?_⟩
    intro ψ
    exact hFB _ ψ.property
  have hFsection := linear_feature_section_tendsto F hFbound φs
  have hFdiff : Tendsto (fun n => ‖F (initialTestSection φs n) - F φs‖)
      atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hFsection
  let qn : ℕ → oscSub p.d m := fun n => initialTestSection φs n
  let u : ℕ → GaussianFeatureHilbert := fun n => J (F (qn n))
  let uLim : GaussianFeatureHilbert := J (F φs)
  let leftSeq : ℕ → Ω → ℝ := fun n ω =>
    OscDual.eval (Z0 t ω) (qn n : Euc p.d → ℝ)
  let rightLim : Ω → ℝ := fun ω => W uLim ω
  have hleftMem : ∀ n, MemLp (leftSeq n) 2 P := by
    intro n
    have hcomp := (gaussianOscEval (qn n)).comp_memLp' (hZ2 t)
    have hEq : ∀ ω, gaussianOscEval (qn n) (Z0 t ω) = leftSeq n ω :=
      fun ω => gaussianOscEval_apply (qn n) (Z0 t ω)
    exact (memLp_congr_ae (Filter.Eventually.of_forall hEq)).1 hcomp
  have hleftTargetMem : MemLp (fun ω => OscDual.eval (Z0 t ω) φ) 2 P :=
    by
      have hcomp := (gaussianOscEval φs).comp_memLp' (hZ2 t)
      have hEq : ∀ ω, gaussianOscEval φs (Z0 t ω) =
          OscDual.eval (Z0 t ω) φ := fun ω => gaussianOscEval_apply φs (Z0 t ω)
      exact (memLp_congr_ae (Filter.Eventually.of_forall hEq)).1 hcomp
  have hleftSqBound : ∀ n,
      ∫ ω, (leftSeq n ω - OscDual.eval (Z0 t ω) φ) ^ 2 ∂P ≤
        (oscNorm m ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 *
          (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P) := by
    intro n
    have hdiffMem : MemLp (fun ω => leftSeq n ω - OscDual.eval (Z0 t ω) φ) 2 P :=
      (hleftMem n).sub hleftTargetMem
    have hmajor : Integrable (fun ω =>
        (oscNorm m ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 *
          ‖Z0 t ω‖ ^ 2) P :=
      (hZ2 t).norm.integrable_sq.const_mul _
    calc
      _ ≤ ∫ ω, (oscNorm m ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 *
          ‖Z0 t ω‖ ^ 2 ∂P := by
        apply integral_mono hdiffMem.integrable_sq hmajor
        intro ω
        have hsub := fp81s21_raw_eval_test_sub (Z0 t ω) (qn n) φs
        have habs := OscDual.abs_eval_le (Z0 t ω)
          ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ) (qn n - φs).property.2
        change (leftSeq n ω - OscDual.eval (Z0 t ω) φ) ^ 2 ≤ _
        rw [show leftSeq n ω - OscDual.eval (Z0 t ω) φ =
          OscDual.eval (Z0 t ω) ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ) by
            simpa [leftSeq, φs] using hsub]
        calc
          _ = |OscDual.eval (Z0 t ω)
              ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)| ^ 2 := by rw [sq_abs]
          _ ≤ (‖Z0 t ω‖ * oscNorm m
              ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).2 habs
          _ = _ := by ring
      _ = (oscNorm m ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 *
          (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P) := by rw [integral_const_mul]
  have hsectionCoord : ∀ n,
      leftSeq n =ᵐ[P] fun ω => W (u n) ω := by
    intro n
    have hcoords := hcoord t ht
    have hseries := fp81s21_series_linear e ξ W hstd hW2 hWlim
    have hsum := fp81s21_raw_W_finset_linear W hseries
      (fun α : MultiIndex p.d => J (F (initialTestBasis m α)))
      (fun α => oscEigenvalue p.d α ^ (m / 2) * HRS.Whole.hermiteCoeff φs α)
      (mova2_S p.d n)
    have hfeature : J (F (qn n)) =
        ∑ α ∈ mova2_S p.d n,
          (oscEigenvalue p.d α ^ (m / 2) * HRS.Whole.hermiteCoeff φs α) •
            J (F (initialTestBasis m α)) := by
      simp only [qn, initialTestSection, F, map_sum, map_smul]
    filter_upwards [hcoords, hsum] with ω hω hsumω
    have heval := initialTestSection_eval φs n (Z0 t ω)
    rw [show (leftSeq n ω) = OscDual.eval (Z0 t ω)
      (initialTestSection φs n : Euc p.d → ℝ) by rfl, heval]
    have hcoordSum : ∀ α ∈ mova2_S p.d n,
        OscDual.coord (Z0 t ω) α = W
          (J (fp81s21_combinedFeature p R hK t (oscTestFun m α))) ω := by
      intro α hα
      have h := hω α
      simpa [m, F, initialTestBasis] using h
    have hsumω' : W (u n) ω = ∑ α ∈ mova2_S p.d n,
        (oscEigenvalue p.d α ^ (m / 2) * HRS.Whole.hermiteCoeff φs α) *
          W (J (F (initialTestBasis m α))) ω := by
      change W (J (F (qn n))) ω = _
      rw [hfeature]
      exact hsumω
    have hsumCoord : (∑ α ∈ mova2_S p.d n,
        (oscEigenvalue p.d α ^ (m / 2) * HRS.Whole.hermiteCoeff φs α) *
          OscDual.coord (Z0 t ω) α) =
        ∑ α ∈ mova2_S p.d n,
          (oscEigenvalue p.d α ^ (m / 2) * HRS.Whole.hermiteCoeff φs α) *
            W (J (F (initialTestBasis m α))) ω := by
      refine Finset.sum_congr rfl ?_
      intro α hα
      rw [hcoordSum α hα]
      rfl
    rw [hsumCoord]
    exact hsumω'.symm
  have hleftTail : Tendsto (fun n =>
      (oscNorm m ((qn n - φs : oscSub p.d m) : Euc p.d → ℝ)) ^ 2 *
        (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P)) atTop (𝓝 0) := by
    have hnorm := fp81s21_raw_eval_section_tail_norm φs
    simpa [qn] using (hnorm.pow 2).mul_const (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P)
  have hleftErr : Tendsto (fun n =>
      ∫ ω, (leftSeq n ω - OscDual.eval (Z0 t ω) φ) ^ 2 ∂P) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _)
      hleftSqBound hleftTail
  have hleftT : HRS.TendstoL2 P leftSeq (fun ω => OscDual.eval (Z0 t ω) φ) :=
    HRS.tendstoL2_of_memLp hleftTargetMem hleftMem hleftErr
  have hrightMem : ∀ n, MemLp (fun ω => W (u n) ω) 2 P := fun n => hW2 (u n)
  have hrightDist : ∀ n,
      (∫ ω, (W (u n) ω - W uLim ω) ^ 2 ∂P) = ‖u n - uLim‖ ^ 2 := by
    intro n
    exact fp81s21_series_distance e ξ W hParseval hstd hW2 hWlim (u n) uLim
  have hJdiff : ∀ n, ‖u n - uLim‖ = ‖F (qn n) - F φs‖ := by
    intro n
    change ‖J (F (qn n)) - J (F φs)‖ = _
    rw [← map_sub]
    exact J.norm_map _
  have hrightErr : Tendsto (fun n =>
      ∫ ω, (W (u n) ω - W uLim ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hnormSq : Tendsto (fun n => ‖F (qn n) - F φs‖ ^ 2) atTop (𝓝 0) := by
      simpa using hFdiff.pow 2
    have heq : ∀ n, (∫ ω, (W (u n) ω - W uLim ω) ^ 2 ∂P) =
        ‖F (qn n) - F φs‖ ^ 2 := by
      intro n
      rw [hrightDist n, hJdiff n]
    exact hnormSq.congr fun n => (heq n).symm
  have hrightT : HRS.TendstoL2 P (fun n ω => W (u n) ω) rightLim :=
    HRS.tendstoL2_of_memLp (hW2 uLim) hrightMem hrightErr
  have hleftToRightErr : Tendsto (fun n =>
      ∫ ω, (leftSeq n ω - rightLim ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, (leftSeq n ω - rightLim ω) ^ 2 ∂P) =
        ∫ ω, (W (u n) ω - rightLim ω) ^ 2 ∂P := by
      intro n
      apply integral_congr_ae
      filter_upwards [hsectionCoord n] with ω hω
      simp [leftSeq, rightLim, hω]
    exact hrightErr.congr fun n => (heq n).symm
  have hleftToRight : HRS.TendstoL2 P leftSeq rightLim :=
    HRS.tendstoL2_of_memLp (hW2 uLim) hleftMem hleftToRightErr
  exact HRS.TendstoL2.ae_unique (fun n => (hleftMem n).aestronglyMeasurable)
    hleftT hleftToRight

#print axioms fp81s21_raw_eval

end HRS.Fp81.S21

end
