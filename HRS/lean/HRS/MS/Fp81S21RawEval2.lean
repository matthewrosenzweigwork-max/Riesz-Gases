import HRS.MS.Fp81S21RawEval
import HRS.MS.S21K2_P07D

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2

/-- The exact raw-family conjuncts following the feature witnesses in
`fp81s21_rawGaussianFamily`, including the coordinate trace that precedes
those witnesses. -/
def fp81s21_rawGaussianBundleSpec
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (V : ℝ)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ)) : Prop :=
  (0 ≤ V ∧ ∀ t : ℝ, 0 ≤ t →
    Summable (fun α : MultiIndex p.d =>
      ‖fp81s21_combinedFeature p R hK t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ∧
    (∑' α : MultiIndex p.d,
      ‖fp81s21_combinedFeature p R hK t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ≤ V) ∧
  (∀ h h' : GaussianFeatureHilbert,
    HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h')) ∧
  HRS.IsStdGaussianSeq P ξ ∧
  (∀ h, Measurable (W h)) ∧
  (∀ h, MemLp (W h) 2 P) ∧
  (∀ h, Tendsto (fun m : ℕ =>
    ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
      atTop (𝓝 0)) ∧
  (∀ r t : ℝ, 0 ≤ r → 0 ≤ t →
    ∀ ψ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      ∫ ω, W (J (fp81s21_combinedFeature p R hK r ψ)) ω *
          W (J (fp81s21_combinedFeature p R hK t φ)) ω ∂P =
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ) ∧
  (∀ (n : ℕ) (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ),
    (∀ i, 0 ≤ τ i) →
    (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
    HRS.IsCenteredGaussian
      (P.map fun ω i => W (J (fp81s21_combinedFeature p R hK
        (τ i) (φ i))) ω)) ∧
  (∀ t, Measurable (Z0 t)) ∧
  (∀ t, MemLp (Z0 t) 2 P) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
    OscDual.coord (Z0 t ω) α =
      W (J (fp81s21_combinedFeature p R hK t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ∧
  (∀ t : ℝ,
    (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P) =
      ∑' α : MultiIndex p.d,
        ∫ ω, (W (J (fp81s21_combinedFeature p R hK (max t 0)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ^ 2 ∂P)

/-- The all-test evaluation lemma applied to the complete abstract bundle
exported by `fp81s21_rawGaussianFamily`. -/
theorem fp81s21_raw_eval_bundle
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (V : ℝ)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ))
    (hBundle : fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0)
    (hFeatureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ)
    (t : ℝ) (ht : 0 ≤ t) (φ : Euc p.d → ℝ)
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    (fun ω => OscDual.eval (Z0 t ω) φ) =ᵐ[P]
      fun ω => W (J (fp81s21_combinedFeature p R hK t φ)) ω := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  rcases hBundle with ⟨_, hParseval, hstd, _, hW2, hWlim, _, _, _, hZ2, hcoord, _⟩
  exact fp81s21_raw_eval p hδ hδhalf R hμ₀ hK J e ξ W Z0
    hParseval hstd hW2 hWlim hZ2 hcoord hFeatureBound t ht φ hφ

/-- The covariance matrix of the raw all-test vector, in the exact physical
normalization exported by the `S21E` definitions. -/
def fp81s21_rawJointCovariance
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {n : ℕ}
    (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => HRS.Whole.linearGaussianCov (r26t3_coeff R) p.β⁻¹
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    (τ i) (τ j) (φ i) (φ j)

/-- The raw oscillator observations at arbitrary finitely many nonnegative
times have exactly the multivariate Gaussian law with the physical covariance
matrix. Positive semidefiniteness and the law are obtained together from the
retained centered-Gaussian vector and its mixed second moments. -/
theorem fp81s21_raw_joint_law
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (V : ℝ)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ))
    (hBundle : fp81s21_rawGaussianBundleSpec (P := P) p R hK V J e ξ W Z0)
    (hFeatureBound : ∀ t : ℝ, 0 ≤ t → ∃ B : ℝ, 0 ≤ B ∧
      ∀ ψ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
        ‖fp81s21_combinedFeature p R hK t ψ‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) ψ)
    (n : ℕ) (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ)
    (hτ : ∀ i, 0 ≤ τ i)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) :
    (fp81s21_rawJointCovariance p R τ φ).PosSemidef ∧
      HRS.law P (fun ω => (WithLp.toLp 2 fun i =>
        OscDual.eval (Z0 (τ i) ω) (φ i) : EuclideanSpace ℝ (Fin n))) =
        ProbabilityTheory.multivariateGaussian 0
          (fp81s21_rawJointCovariance p R τ φ) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  have hBundle₀ := hBundle
  rcases hBundle with ⟨_, hParseval, hstd, hWm, hW2, hWlim, hCov, hJoint,
    hZmeas, hZ2, hcoord, _⟩
  let G : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i =>
    OscDual.eval (Z0 (τ i) ω) (φ i)
  let X : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun i =>
    W (J (fp81s21_combinedFeature p R hK (τ i) (φ i))) ω
  have hGm : Measurable G := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    refine measurable_pi_iff.2 fun i => ?_
    have he : (fun ω => OscDual.eval (Z0 (τ i) ω) (φ i)) =
        (gaussianOscEval ⟨φ i, hφ i⟩) ∘ Z0 (τ i) := by
      funext ω
      exact (gaussianOscEval_apply ⟨φ i, hφ i⟩ _).symm
    rw [he]
    exact (gaussianOscEval ⟨φ i, hφ i⟩).continuous.measurable.comp
      (hZmeas (τ i))
  have heval : ∀ i,
      (fun ω => OscDual.eval (Z0 (τ i) ω) (φ i)) =ᵐ[P]
        fun ω => W (J (fp81s21_combinedFeature p R hK (τ i) (φ i))) ω := by
    intro i
    exact fp81s21_raw_eval_bundle p hδ hδhalf R hμ₀ hK V J e ξ W Z0
      hBundle₀ hFeatureBound (τ i) (hτ i) (φ i) (hφ i)
  have hvec : G =ᵐ[P] X := by
    have hall : ∀ᵐ ω ∂P, ∀ i, G ω i = X ω i := by
      filter_upwards [ae_all_iff.2 heval] with ω hω i
      simpa [G, X] using hω i
    filter_upwards [hall] with ω hω
    ext i
    exact hω i
  have hFm : Measurable (fun ω i => W (J (fp81s21_combinedFeature p R hK
      (τ i) (φ i))) ω) := measurable_pi_iff.2 fun i => hWm _
  let toEuclidean : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap
  have hXeq : X = toEuclidean ∘ (fun ω i =>
      W (J (fp81s21_combinedFeature p R hK (τ i) (φ i))) ω) := by
    funext ω
    rfl
  have hXmap : HRS.law P X =
      (P.map (fun ω i => W (J (fp81s21_combinedFeature p R hK
        (τ i) (φ i))) ω)).map toEuclidean := by
    rw [hXeq]
    exact (toEuclidean.continuous.measurable.aemeasurable.map_map_of_aemeasurable
      hFm.aemeasurable).symm
  have hcenterX : HRS.IsCenteredGaussian (HRS.law P X) := by
    rw [hXmap]
    have hJ := hJoint n τ φ hτ hφ
    letI : IsGaussian (P.map (fun ω i =>
        W (J (fp81s21_combinedFeature p R hK (τ i) (φ i))) ω)) := hJ.1
    refine ⟨inferInstance, fun L => ?_⟩
    rw [integral_map toEuclidean.continuous.measurable.aemeasurable
      L.continuous.aestronglyMeasurable]
    exact hJ.2 (L.comp toEuclidean)
  have hcenter : HRS.IsCenteredGaussian (HRS.law P G) := by
    have hLaw : HRS.law P G = P.map X := by
      change P.map G = P.map X
      exact Measure.map_congr hvec
    rw [hLaw]
    exact hcenterX
  have hcov : ∀ i j, ∫ ω, G ω i * G ω j ∂P =
      fp81s21_rawJointCovariance p R τ φ i j := by
    intro i j
    calc
      _ = ∫ ω,
          W (J (fp81s21_combinedFeature p R hK (τ i) (φ i))) ω *
          W (J (fp81s21_combinedFeature p R hK (τ j) (φ j))) ω ∂P := by
        apply integral_congr_ae
        filter_upwards [heval i, heval j] with ω hi hj
        simp [G, hi, hj]
      _ = HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ
            (τ i) (τ j) (φ i) (φ j) := hCov (τ i) (τ j) (hτ i) (hτ j)
              (φ i) (φ j) (hφ i) (hφ j)
      _ = fp81s21_rawJointCovariance p R τ φ i j := by
        simp [fp81s21_rawJointCovariance, HRS.MS.S21E.s21eCov,
          HRS.Whole.linearGaussianCov, r26t3_coeff, r26t3_mu]
  have hLaw := HRS.MS.R26T3.s21k2_p07_law_eq
    (G := G) (hG := ⟨hGm.aestronglyMeasurable, hcenter⟩) hcov
  simpa [HRS.MS.R26T3.s21k2_p07_gam] using hLaw

#print axioms fp81s21_raw_eval_bundle
#print axioms fp81s21_raw_joint_law

end HRS.Fp81.S21

end
