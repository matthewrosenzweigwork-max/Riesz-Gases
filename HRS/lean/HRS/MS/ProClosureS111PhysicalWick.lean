import HRS.MS.ProClosureS111CovarianceAllTime
import HRS.MS.ProClosureS111GaussianLaw
import HRS.MS.S111X2Aux42
import HRS.MS.R2ChaosAux6

/-!
Actual scalar Wick chaoses of the physical Gaussian evolution.  The Gaussian
sequence estimate is produced from the physical all-time centered covariance
bound, rather than assumed as an extra field or particle-convergence input.
The underlying probability space and the native compact-test basis are kept.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6
open HRS.MS.R2Chaos

variable {d : ℕ} {m : ℝ}

theorem gaussianTest_ofFun_smul (c : ℝ) (phi : oscSub d m) :
    OscSpace.ofFun m ((c • phi : oscSub d m) : Euc d → ℝ) =
      c • OscSpace.ofFun m (phi : Euc d → ℝ) := by
  apply lp.ext
  funext alpha
  change OscSpace.coord (OscSpace.ofFun m ((c • phi : oscSub d m) : Euc d → ℝ)) alpha =
    OscSpace.coord (c • OscSpace.ofFun m (phi : Euc d → ℝ)) alpha
  have hsmul : OscSpace.coord (c • OscSpace.ofFun m (phi : Euc d → ℝ)) alpha =
      c * OscSpace.coord (OscSpace.ofFun m (phi : Euc d → ℝ)) alpha := by
    show ((c • (show lp (fun _ : MultiIndex d => ℝ) 2 from
      OscSpace.ofFun m (phi : Euc d → ℝ)) : lp (fun _ : MultiIndex d => ℝ) 2) alpha) = _
    rw [lp.coeFn_smul]
    simp only [Pi.smul_apply, smul_eq_mul, OscSpace.coord]
  rw [hsmul, OscSpace.coord_ofFun_eq (c • phi).property.2,
    OscSpace.coord_ofFun_eq phi.property.2]
  have hc : HRS.Whole.hermiteCoeff ((c • phi : oscSub d m) : Euc d → ℝ) alpha =
      c * HRS.Whole.hermiteCoeff (phi : Euc d → ℝ) alpha := by
    change (∫ x, (c * (phi : Euc d → ℝ) x) * hermiteFunD alpha x) =
      c * ∫ x, (phi : Euc d → ℝ) x * hermiteFunD alpha x
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hc]
  ring

/-- The actual test embedding, as a linear map on the original test submodule. -/
def gaussianTestEmbedding (d : ℕ) (m : ℝ) : oscSub d m →ₗ[ℝ] OscSpace d m where
  toFun phi := OscSpace.ofFun m (phi : Euc d → ℝ)
  map_add' phi psi := by
    have hn : OscSpace.ofFun m ((-psi : oscSub d m) : Euc d → ℝ) =
        -OscSpace.ofFun m (psi : Euc d → ℝ) := by
      rw [← neg_one_smul ℝ psi]
      rw [← neg_one_smul ℝ (OscSpace.ofFun m (psi : Euc d → ℝ))]
      exact gaussianTest_ofFun_smul (-1) psi
    have h := initialTest_ofFun_sub phi (-psi)
    simpa only [sub_neg_eq_add, hn] using h
  map_smul' c phi := gaussianTest_ofFun_smul c phi

def gaussianTestEvaluation (z : OscDual d m) : oscSub d m →ₗ[ℝ] ℝ :=
  (OscDual.toDual z).toLinearMap.comp (gaussianTestEmbedding d m)

theorem gaussianTestEvaluation_apply (z : OscDual d m) (phi : oscSub d m) :
    gaussianTestEvaluation z phi = OscDual.eval z (phi : Euc d → ℝ) :=
  OscDual.toDual_ofFun z _ phi.property.2

theorem r2Test_isOscTest (m : ℝ) {f : Euc d → ℝ} (hf : IsR2Test f) :
    IsOscTest m f :=
  ⟨hf.1, memOsc_schwartz m (hf.2.toSchwartzMap hf.1)⟩

section GaussianObservation

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {C : WholeCoeff d} {q H : ℝ}
variable {C0 : (Euc d → ℝ) → (Euc d → ℝ) → ℝ}
variable {Z : ℝ → Omega → OscDual d m}

/-- One actual observation has its prescribed second moment, including the
degenerate zero-variance case. Positivity is checked explicitly before the
prescribed matrix is identified as the actual Gaussian covariance. -/
theorem gaussian_observation_law_and_second
    (hZ : IsLinearGaussianEvolutionW P C m q H C0 Z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (phi : oscSub d m)
    (hK : 0 ≤ linearGaussianCov C q C0 t t phi phi) :
    (∃ v : ℝ≥0, P.map (fun w => OscDual.eval (Z t w) (phi : Euc d → ℝ)) =
      gaussianReal 0 v) ∧
      (∫ w, OscDual.eval (Z t w) (phi : Euc d → ℝ) ^ 2 ∂P) =
        linearGaussianCov C q C0 t t phi phi := by
  let X : Omega → ℝ := fun w => OscDual.eval (Z t w) (phi : Euc d → ℝ)
  have hXm : Measurable X := by
    have he : X = fun w => gaussianOscEval phi (Z t w) := by
      funext w
      exact (gaussianOscEval_apply phi _).symm
    rw [he]
    exact (gaussianOscEval phi).continuous.measurable.comp (hZ.meas t)
  let V : Omega → EuclideanSpace ℝ (Fin 1) := fun w => WithLp.toLp 2 (fun _ => X w)
  have hVm : Measurable V :=
    (WithLp.measurable_toLp 2 (Fin 1 → ℝ)).comp (measurable_pi_iff.2 fun _ => hXm)
  let K : ℝ := linearGaussianCov C q C0 t t phi phi
  let S : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => K
  have hS : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      rfl
    · simp only [S, dotProduct, Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_one,
        star_trivial]
      have hp : 0 ≤ K * (x 0) ^ 2 := mul_nonneg hK (sq_nonneg (x 0))
      nlinarith [hp]
  have hLaw : P.map V = multivariateGaussian 0 S := by
    exact hZ.gaussian 1 (fun _ => t) (fun _ => (phi : Euc d → ℝ))
      (fun _ => ht) (fun _ => phi.property)
  have hG : HRS.IsCenteredGaussian (P.map V) := by
    rw [hLaw]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg 1 S
  let ell : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hmap : P.map X = (P.map V).map ell := by
    rw [Measure.map_map ell.continuous.measurable hVm]
    rfl
  haveI : IsGaussian (P.map V) := hG.1
  have hreal := IsGaussian.map_eq_gaussianReal (μ := P.map V) ell
  have hmean := hG.2 ell
  constructor
  · refine ⟨(ProbabilityTheory.variance ell (P.map V)).toNNReal, ?_⟩
    rw [hmap, hreal, hmean]
  · have hsecond := s111x2_gauss_mixed S hS (0 : Fin 1) 0
    rw [← hLaw, integral_map hVm.aemeasurable
      (show AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 1) => x 0 * x 0) (P.map V)
        from (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin 1) => x 0 * x 0)).aestronglyMeasurable)]
      at hsecond
    change (∫ w, X w * X w ∂P) = K at hsecond
    simpa only [sq] using hsecond

end GaussianObservation

/-- The centered physical Gaussian sequence estimate for the native compact
basis. The same constant works for all horizons, times, preparations, and
realizations of the prescribed physical Gaussian evolution. -/
theorem physical_gaussian_sequence_uniform (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 < L ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ)
        (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
        (wholeSpaceIndex d) beta⁻¹ H
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z →
      ∀ basis : ℕ → Euc d → ℝ,
      IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ t ∈ Icc (0 : ℝ) H,
        S94GSeq P (fun i w => OscDual.eval (Z t w) (basis i)) L := by
  obtain ⟨L, hL, hcov⟩ := physical_covariance_all_time hd s a beta hs0 hs ha hbeta
  refine ⟨L, hL, fun rho hrho gamma hgamma Omega _ P _ H Z hZ basis hbasis t ht n => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  let test : Fin n → oscSub d (wholeSpaceIndex d) := fun i =>
    ⟨basis i, r2Test_isOscTest _ (hbasis.1 i)⟩
  let psi : (Fin n → ℝ) → oscSub d (wholeSpaceIndex d) := fun alpha =>
    ∑ i, alpha i • test i
  have hlin : ∀ alpha : Fin n → ℝ,
      (fun w => s94lin (fun i : Fin n => fun w => OscDual.eval (Z t w) (basis i)) alpha w) =
        fun w => OscDual.eval (Z t w) (psi alpha : Euc d → ℝ) := by
    intro alpha
    funext w
    rw [← gaussianTestEvaluation_apply (Z t w) (psi alpha)]
    simp only [psi, map_sum, map_smul, gaussianTestEvaluation_apply, test, smul_eq_mul,
      s94lin]
  have hsingle : ∀ alpha : Fin n → ℝ,
      (∃ v : ℝ≥0, P.map (fun w => OscDual.eval (Z t w) (psi alpha : Euc d → ℝ)) =
        gaussianReal 0 v) ∧
      (∫ w, OscDual.eval (Z t w) (psi alpha : Euc d → ℝ) ^ 2 ∂P) =
        linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma) t t (psi alpha) (psi alpha) := by
    intro alpha
    exact gaussian_observation_law_and_second hZ ht (psi alpha)
      (hcov rho hrho gamma hgamma t ht.1 _ (psi alpha).property).1
  constructor
  · refine ⟨fun i => ?_, fun alpha => ?_⟩
    · have hm := (gaussianOscEval (test i)).continuous.measurable.comp (hZ.meas t)
      have he : (fun w => gaussianOscEval (test i) (Z t w)) =
          fun w => OscDual.eval (Z t w) (basis i) := by
        funext w
        exact gaussianOscEval_apply (test i) _
      change AEMeasurable (fun w => OscDual.eval (Z t w) (basis i)) P
      rw [← he]
      exact hm.aemeasurable
    · change ∃ v : ℝ≥0, P.map (fun w => s94lin
        (fun i : Fin n => fun w => OscDual.eval (Z t w) (basis i)) alpha w) = gaussianReal 0 v
      rw [hlin alpha]
      exact (hsingle alpha).1
  · intro alpha
    unfold s94q
    change (∫ w, s94lin
      (fun i : Fin n => fun w => OscDual.eval (Z t w) (basis i)) alpha w ^ 2 ∂P) ≤
      L * ∑ i, alpha i ^ 2
    have hInt : (∫ w, s94lin
        (fun i : Fin n => fun w => OscDual.eval (Z t w) (basis i)) alpha w ^ 2 ∂P) =
        ∫ w, OscDual.eval (Z t w) (psi alpha : Euc d → ℝ) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with w
      exact congrArg (fun z : ℝ => z ^ 2) (congrFun (hlin alpha) w)
    have hcov' := (hcov rho hrho gamma hgamma t ht.1 _ (psi alpha).property).2
    have he : (psi alpha : Euc d → ℝ) = fun x => ∑ i : Fin n, alpha i * basis i x := by
      funext x
      simp [psi, test]
    calc
      _ = ∫ w, OscDual.eval (Z t w) (psi alpha : Euc d → ℝ) ^ 2 ∂P := hInt
      _ = linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma) t t
            (psi alpha) (psi alpha) := (hsingle alpha).2
      _ ≤ L * ∫ x, HRS.Whole.projMean mu (psi alpha : Euc d → ℝ) x ^ 2 ∂mu := hcov'
      _ = L * ∑ i, alpha i ^ 2 := by
        rw [he, s94_projMean_sq_lincomb mu (fun i : Fin n => hbasis.1 i)
          (fun i j : Fin n => by simpa [Fin.ext_iff] using hbasis.2.1 i j) alpha]

/-- Actual scalar physical Wick realization for every symmetric L² kernel.
This consumes no Gaussian-sequence bound: that bound is produced above from
the thermal data and the exact physical Gaussian law. -/
theorem physical_wick_exists_uniform (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 < L ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ)
        (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
        (wholeSpaceIndex d) beta⁻¹ H
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z →
      ∀ basis : ℕ → Euc d → ℝ,
      IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ t ∈ Icc (0 : ℝ) H, ∀ k : Euc d → Euc d → ℝ,
      Measurable (fun xy : Euc d × Euc d => k xy.1 xy.2) →
      (∀ x y, k x y = k y x) →
      MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2
        ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) →
      ∃ Q : Omega → ℝ, MemLp Q 2 P ∧
        IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
          (fun i w => OscDual.eval (Z t w) (basis i)) k Q ∧
        (∫ w, Q w ^ 2 ∂P) ≤ 2 * L ^ 2 *
          ∫ xy, k xy.1 xy.2 ^ 2 ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) := by
  obtain ⟨L, hL, hseq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  refine ⟨L, hL, fun rho hrho gamma hgamma Omega _ P _ H Z hZ basis hbasis t ht k hkm hks hk2 => ?_⟩
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hz := hseq rho hrho gamma hgamma Omega P H Z hZ basis hbasis t ht
  obtain ⟨Q, hQ, hbound⟩ := s94_wick_exists hz hL.le hbasis.1 hbasis.2.1 hkm hks hk2
  exact ⟨Q, hQ.1, hQ.isWick hz, hbound⟩

end HRS.MS.ProClosureS111
