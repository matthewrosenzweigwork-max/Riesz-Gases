import HRS.MS.Fp81S21RealizeAll5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- Finite linearity of the retained series limit, on its original source. -/
private theorem fp81s21_source_finset_linear_retained
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω -
        W h ω) ^ 2 ∂P) atTop (𝓝 0))
    {ι : Type*} (f : ι → GaussianFeatureHilbert) (c : ι → ℝ)
    (S : Finset ι) :
    W (∑ i ∈ S, c i • f i) =ᵐ[P]
      fun ω => ∑ i ∈ S, c i * W (f i) ω := by
  have hl := fp81s21_series_linear e ξ W hstd hW2 hWlim
  induction S using Finset.induction_on with
  | empty =>
      have hz := hl 0 0 1
      filter_upwards [hz] with ω hω
      simpa using (show W 0 ω = 0 by
        simp only [add_zero, one_smul] at hω
        linarith)
  | @insert a S ha ih =>
      have hh := hl (∑ i ∈ S, c i • f i) (f a) (c a)
      filter_upwards [hh, ih] with ω hω hS
      rw [Finset.sum_insert ha]
      have he : W (c a • f a + ∑ i ∈ S, c i • f i) ω =
          W (∑ i ∈ S, c i • f i) ω + c a * W (f a) ω := by
        simpa [add_comm, add_left_comm, add_assoc] using hω
      rw [he, hS]
      simp only [Finset.sum_insert ha]
      ring

/-- The retained series gives Gaussian laws for every finite family of
features, without choosing a second probability space or source. -/
private theorem fp81s21_source_joint_law_retained
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h')
        (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω -
        W h ω) ^ 2 ∂P) atTop (𝓝 0))
    (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert) :
    P.map (fun ω => ∑ i, c i * W (f i) ω) =
      gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)) := by
  let u : GaussianFeatureHilbert := ∑ i, c i • f i
  have hsum : Summable (fun j => (inner ℝ (e j) u) ^ 2) := by
    simpa [sq] using (hParseval u u).summable
  have htsum : (∑' j, (inner ℝ (e j) u) ^ 2) = ‖u‖ ^ 2 := by
    have ht := (hParseval u u).tsum_eq
    simpa [sq, real_inner_self_eq_norm_sq] using ht
  have hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨hstd.aemeasurable i,
      by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩
  have hWlaw : P.map (W u) =
      gaussianReal 0 (Real.toNNReal (‖u‖ ^ 2)) := by
    have hlaw := s21g2_s11a_law hξlaw hstd.1
      (fun j => inner ℝ (e j) u) hsum (hW2 u) (hWlim u)
    rw [htsum] at hlaw
    exact hlaw
  have hlinear := fp81s21_source_finset_linear_retained
    e ξ W hstd hW2 hWlim f c Finset.univ
  have hmap : P.map (fun ω => ∑ i, c i * W (f i) ω) = P.map (W u) := by
    apply Measure.map_congr
    filter_upwards [hlinear] with ω hω
    simpa [u] using hω.symm
  calc
    P.map (fun ω => ∑ i, c i * W (f i) ω) = P.map (W u) := hmap
    _ = gaussianReal 0 (Real.toNNReal (‖u‖ ^ 2)) := hWlaw
    _ = gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)) := by
      simp [u]

/-- Covariances of the same retained source, recovered by polarization from
its finite-feature Gaussian laws. -/
private theorem fp81s21_source_covariance_retained
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hWm : ∀ h, Measurable (W h))
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω -
        W h ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJoint : ∀ (n : ℕ) (c : Fin n → ℝ)
      (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))) :
    ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h' := by
  intro h h'
  have hsecond (g : GaussianFeatureHilbert) :
      ∫ ω, W g ω ^ 2 ∂P = ‖g‖ ^ 2 := by
    have hg := hJoint 1 (fun _ => 1) (fun _ => g)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      one_smul] at hg
    calc
      ∫ ω, W g ω ^ 2 ∂P = Real.toNNReal (‖g‖ ^ 2) :=
        s21g2_s11a_second (hWm g).aemeasurable hg
      _ = ‖g‖ ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hi : Integrable (fun ω => W h ω * W h' ω) P :=
    (hW2 h).integrable_mul (hW2 h')
  have hsumInt : ∫ ω, (W h ω + W h' ω) ^ 2 ∂P =
      ∫ ω, W h ω ^ 2 ∂P +
        2 * ∫ ω, W h ω * W h' ω ∂P +
        ∫ ω, W h' ω ^ 2 ∂P := by
    have heq : ∀ ω, (W h ω + W h' ω) ^ 2 =
        W h ω ^ 2 + 2 * (W h ω * W h' ω) + W h' ω ^ 2 := by
      intro ω
      ring
    calc
      ∫ ω, (W h ω + W h' ω) ^ 2 ∂P =
          ∫ ω, W h ω ^ 2 + 2 * (W h ω * W h' ω) + W h' ω ^ 2 ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall heq
      _ = ∫ ω, W h ω ^ 2 ∂P +
            2 * ∫ ω, W h ω * W h' ω ∂P +
            ∫ ω, W h' ω ^ 2 ∂P := by
        rw [integral_add
          (f := fun ω => W h ω ^ 2 + 2 * (W h ω * W h' ω))
          (g := fun ω => W h' ω ^ 2)
          ((hW2 h).integrable_sq.add (hi.const_mul 2))
          (hW2 h').integrable_sq,
          integral_add (f := fun ω => W h ω ^ 2)
            (g := fun ω => 2 * (W h ω * W h' ω))
            (hW2 h).integrable_sq (hi.const_mul 2), integral_const_mul]
  have hlin := fp81s21_series_linear e ξ W hstd hW2 hWlim h h' 1
  have hnormSum : ∫ ω, (W h ω + W h' ω) ^ 2 ∂P =
      ‖h + h'‖ ^ 2 := by
    calc
      ∫ ω, (W h ω + W h' ω) ^ 2 ∂P =
          ∫ ω, W (h + h') ω ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hlin] with ω hω
        have hh : W (h + h') ω = W h ω + W h' ω := by
          simpa using hω
        rw [← hh]
      _ = ‖h + h'‖ ^ 2 := hsecond (h + h')
  have hinner : ‖h + h'‖ ^ 2 =
      ‖h‖ ^ 2 + 2 * inner ℝ h h' + ‖h'‖ ^ 2 := by
    simp [norm_add_sq_real, two_mul, add_assoc, add_left_comm, add_comm]
  have hpair : ‖h + h'‖ ^ 2 =
      ‖h‖ ^ 2 + 2 * ∫ ω, W h ω * W h' ω ∂P + ‖h'‖ ^ 2 := by
    calc
      ‖h + h'‖ ^ 2 = ∫ ω, (W h ω + W h' ω) ^ 2 ∂P := hnormSum.symm
      _ = ∫ ω, W h ω ^ 2 ∂P +
            2 * ∫ ω, W h ω * W h' ω ∂P +
            ∫ ω, W h' ω ^ 2 ∂P := hsumInt
      _ = ‖h‖ ^ 2 + 2 * ∫ ω, W h ω * W h' ω ∂P + ‖h'‖ ^ 2 := by
        rw [hsecond h, hsecond h']
  rw [hinner] at hpair
  linarith

/-- The retained source, its patched continuous realization, and all
same-source Gaussian certificates needed by later physical consumers. -/
structure fp81s21_gaussian_source_retained_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)) where
  Mg : ℝ
  K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)
  hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg
  V : ℝ
  J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert
  G0 : GaussianRealization R
  e : ℕ → GaussianFeatureHilbert
  ξ : ℕ → G0.Ω → ℝ
  W : GaussianFeatureHilbert → G0.Ω → ℝ
  Z0 : ℝ → G0.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ)
  rawBundle : @fp81s21_rawGaussianBundleSpec p δ R hμ₀ Mg K hK V J
    G0.Ω G0.mΩ G0.P G0.prob e ξ W Z0
  featureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
    ∀ ψ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ
  localIncrement : ∀ H : ℝ, 0 < H →
    ∃ L : MultiIndex p.d → ℝ,
      (∀ α, 0 ≤ L α) ∧ Summable L ∧
      ∃ C : ℝ, C = 3 * (∑' α, L α) ^ 2 ∧ 0 ≤ C ∧
        ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
          ∫⁻ ω, ‖Z0 t ω - Z0 s ω‖ₑ ^ (4 : ℝ) ∂G0.P ≤
            ENNReal.ofReal (C * |t - s| ^ 2)
  jointProcessMeasurable : Measurable (Function.uncurry G0.Z)
  fixedTimeModification : ∀ t : ℝ, 0 ≤ t → G0.Z t =ᵐ[G0.P] Z0 t
  rawJointLaw : ∀ (n : ℕ) (τ : Fin n → ℝ)
    (φ : Fin n → Euc p.d → ℝ),
    (∀ i, 0 ≤ τ i) →
    (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
    HRS.law G0.P (fun ω => (WithLp.toLp 2 fun i =>
      OscDual.eval (Z0 (τ i) ω) (φ i) :
        EuclideanSpace ℝ (Fin n))) =
      ProbabilityTheory.multivariateGaussian 0
        (fp81s21_rawJointCovariance p R τ φ)
  allFeatureGaussianLaw : ∀ (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → GaussianFeatureHilbert),
    G0.P.map (fun ω => ∑ i, c i * W (f i) ω) =
      gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))
  allFeatureCovariance : ∀ h h' : GaussianFeatureHilbert,
    ∫ ω, W h ω * W h' ω ∂G0.P = inner ℝ h h'
  ξAemeasurable : ∀ n, AEMeasurable (ξ n) G0.P
  sourceEvaluation : ∀ t : ℝ, 0 ≤ t →
    ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
        (fun ω => OscDual.eval (G0.Z t ω) φ) =ᵐ[G0.P]
          fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω

/-- One source is retained through the raw evaluation, fixed-time patching,
and all-horizon Gaussian evolution.  The arbitrary-feature laws and
covariances are recovered from this same source's convergent series. -/
theorem fp81s21_gaussian_source_retained (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ R : Trajectory p δ,
          Nonempty (fp81s21_gaussian_source_retained_data p R
            (fp81s21_initialMeasure_isProbability p R)) := by
  obtain ⟨δ₀, hδ₀, hδ₀half, hretained⟩ :=
    fp81s21_realize_retained_bundle p
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R
  let hμ₀ : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ₀half
  rcases hretained δ hδ hδle R hμ₀ with
    ⟨Mg, K, hK, V, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
      hBundle0, hNorm, hFeatureBound⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hBundle := hBundle0
  rcases hBundle0 with
    ⟨hTrace, hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZmem, hcoord, hZsecond⟩
  have hBundle' : fp81s21_rawGaussianBundleSpec
      (P := P) p R hK V J e ξ W Z0 :=
    ⟨hTrace, hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZmem, hcoord, hZsecond⟩
  have hLocal := fp81s21_realize_local_modifications Z0 hZmeas hNorm
  rcases hLocal with ⟨Y, hYmeas, hYmod⟩
  obtain ⟨Z, hZjoint, hZcont, hmod⟩ :=
    fp81s21_realize_patched_process Z0 Y hYmeas hYmod
  have hZmeas' : ∀ t, Measurable (Z t) := by
    intro t
    have hslice : Measurable (fun ω : Ω => (t, ω)) :=
      measurable_prodMk_left
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
    exact (fp81s21_raw_joint_law p hδ hδhalf R hμ₀ hK V J e ξ W Z0
      hBundle' hFeatureBound n τ φ hτ hφ).2
  have hEvolution := fp81s21_realize_evolution_all_horizons R Z Z0
    hZmeas' hZcont hmod hRawLaw
  let G0 : GaussianRealization R := ⟨Ω, P, Z, hEvolution⟩
  have hSourceJoint := fp81s21_source_joint_law_retained
    P e ξ W hParseval hstd hW2 hWlim
  have hSourceCov := fp81s21_source_covariance_retained
    P e ξ W hstd hWmeas hW2 hWlim hSourceJoint
  have hξAemeasurable : ∀ n, AEMeasurable (ξ n) P :=
    fun n => hstd.aemeasurable n
  have hSourceEval : ∀ t : ℝ, 0 ≤ t →
      ∀ φ : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          (fun ω => OscDual.eval (Z t ω) φ) =ᵐ[P]
            fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω := by
    intro t ht φ hφ
    have heval := fp81s21_raw_eval_bundle p hδ hδhalf R hμ₀ hK V J
      e ξ W Z0 hBundle' hFeatureBound t ht φ hφ
    filter_upwards [hmod t ht, heval] with ω hpatch he
    calc
      OscDual.eval (Z t ω) φ = OscDual.eval (Z0 t ω) φ := by
        exact congrArg (fun z : OscDual p.d (wholeSpaceIndex p.d : ℝ) =>
          OscDual.eval z φ) hpatch
      _ = W (J (fp81s21_combinedFeature p R hK t φ)) ω := he
  refine ⟨{
    Mg := Mg
    K := K
    hK := hK
    V := V
    J := J
    G0 := G0
    e := e
    ξ := ξ
    W := W
    Z0 := Z0
    rawBundle := hBundle'
    featureBound := hFeatureBound
    localIncrement := hNorm
    jointProcessMeasurable := hZjoint
    fixedTimeModification := hmod
    rawJointLaw := hRawLaw
    allFeatureGaussianLaw := hSourceJoint
    allFeatureCovariance := hSourceCov
    ξAemeasurable := hξAemeasurable
    sourceEvaluation := by
      simpa [G0] using hSourceEval
  }⟩

#print axioms fp81s21_gaussian_source_retained
#print axioms fp81s21_source_joint_law_retained
#print axioms fp81s21_source_covariance_retained
#print axioms fp81s21_source_finset_linear_retained

end HRS.Fp81.S21
end
