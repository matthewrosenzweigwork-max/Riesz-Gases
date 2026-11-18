import HRS.MS.Fp81S21InitialFam2
import HRS.MS.Fp81S21InitialStein3
import HRS.MS.R2SeAux5
import HRS.MS.R2SeAux8
import HRS.MS.R2SeAux14

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open S99
open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- The initial-law susceptibility covariance coefficient. -/
def fp81s21_initialCf {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (φ ψ : Euc p.d → ℝ) : ℝ :=
  HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ φ ψ

/-- The actual nonthermal quadratic statistic, centered under `r26t3_Q R N`. -/
def fp81s21_initialBq {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (χ : Euc p.d → ℝ) (N : ℕ) (X : EucConfig p.d N) : ℝ :=
  (N : ℝ) * (HRS.Whole.pairEnergy (HRS.Whole.commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
    ∫ Y, HRS.Whole.pairEnergy (HRS.Whole.commutatorKernel p.d p.s (gradient χ)) Y (r26t3_mu R 0)
      ∂(r26t3_Q R N))

/-- Integrate a countable family termwise under a probability measure from a summable uniform bound. -/
theorem fp81s21_integral_tsum {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : ι → α → ℝ} {M : ι → ℝ}
    (hM : Summable M) (hmeas : ∀ i, AEStronglyMeasurable (g i) μ)
    (hbound : ∀ i x, |g i x| ≤ M i) :
    ∑' i, ∫ x, g i x ∂μ = ∫ x, ∑' i, g i x ∂μ := by
  have hint : ∀ i, Integrable (g i) μ := fun i =>
    Integrable.of_bound (hmeas i) (M i) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hbound i x)
  refine integral_tsum_of_summable_integral_norm hint ?_
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hM
  calc ∫ x, ‖g i x‖ ∂μ ≤ ∫ x, M i ∂μ :=
        integral_mono (hint i).norm (integrable_const _) (fun x => by
          rw [Real.norm_eq_abs]
          exact hbound i x)
    _ = M i := by simp

/-- Bounded `C¹` test data for a single coordinate derivative of the initial feature map. -/
theorem fp81s21_initial_testData
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {f : SeqL2 → ℝ} (hf : SteinCl f) {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ContDiff ℝ 1 (fun X : EucConfig p.d N =>
      pd f j (featureVec φ (r26t3_marg R N) X)) ∧
    (∀ X : EucConfig p.d N, |pd f j (featureVec φ (r26t3_marg R N) X)| ≤ 1) ∧
    (∀ X : EucConfig p.d N, ‖fderiv ℝ (fun Y : EucConfig p.d N =>
      pd f j (featureVec φ (r26t3_marg R N) Y)) X‖ ≤
        Real.sqrt N * ∑' k, cbNorm (fp81s21_J1 p.d) (φ k)) := by
  have hN1 : 1 ≤ N := by omega
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let ν := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  have hWcd : ContDiff ℝ 1 W := S99.s99_W_contDiff hN1 hJ hφ
  have hψ : Bd 4 (pd f j) := hf.pd j
  have hψcd : ContDiff ℝ 1 (pd f j) := hψ.1.of_le (by norm_num)
  let b : ℕ → ℝ := fun k => cbNorm (fp81s21_J1 p.d) (φ k)
  have hbs : Summable b := hφ.2
  have hDF : ∀ X, ‖fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X‖ ≤
      Real.sqrt N * ∑' k, b k := by
    intro X
    have hWder := S99.s99_W_hasFDerivAt hN1 hJ hφ (ν := ν) X
    have hder : fderiv ℝ W X =
        ∑' k : ℕ, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)) := hWder.fderiv
    have hLnorm : Summable fun k : ℕ =>
        ‖(s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        (hbs.mul_left (Real.sqrt N))
      exact S99.s99_Wterm_fderiv_norm hN1 hJ hφ.1 k X
    have hnorm : ‖fderiv ℝ W X‖ ≤ Real.sqrt N * ∑' k, b k := by
      rw [hder]
      calc ‖∑' k : ℕ, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))‖
          ≤ ∑' k : ℕ, ‖(s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))‖ :=
            norm_tsum_le_tsum_norm hLnorm
        _ ≤ ∑' k : ℕ, Real.sqrt N * b k := Summable.tsum_le_tsum
            (fun k => S99.s99_Wterm_fderiv_norm hN1 hJ hφ.1 k X) hLnorm
            (hbs.mul_left (Real.sqrt N))
        _ = Real.sqrt N * ∑' k, b k := by rw [← tsum_mul_left]
    have hcomp := (hψcd.differentiable (by norm_num) (W X)).hasFDerivAt.comp X hWder
    have hcompEq : fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X =
        (fderiv ℝ (pd f j) (W X)).comp (fderiv ℝ W X) := by
      change fderiv ℝ (pd f j ∘ W) X =
        (fderiv ℝ (pd f j) (W X)).comp (fderiv ℝ W X)
      rw [hder]
      exact hcomp.fderiv
    rw [hcompEq]
    have hψD : ‖fderiv ℝ (pd f j) (W X)‖ ≤ 1 := hψ.fderiv_le (W X)
    calc ‖(fderiv ℝ (pd f j) (W X)).comp (fderiv ℝ W X)‖
        ≤ ‖fderiv ℝ (pd f j) (W X)‖ * ‖fderiv ℝ W X‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (Real.sqrt N * ∑' k, b k) :=
          mul_le_mul hψD hnorm (norm_nonneg _) (by positivity)
      _ = Real.sqrt N * ∑' k, b k := by ring
  refine ⟨hψcd.comp hWcd, (fun X => hψ.abs_le _), ?_⟩
  intro X
  exact hDF X

/-- The derivative of one coordinate Stein test along the S9.9 corrector field. -/
theorem fp81s21_initial_test_deriv
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∀ X : EucConfig p.d N,
      fderiv ℝ (fun Y : EucConfig p.d N => pd f j
        (featureVec φ (r26t3_marg R N) Y)) X (fun i => gradient (F.χ j) (X i)) =
        Real.sqrt N * ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X) := by
  intro X
  have hN1 : 1 ≤ N := by omega
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  let ν := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun Y => featureVec φ ν Y
  have hψcd : ContDiff ℝ 1 (pd f j) := (hf.pd j).1.of_le (by norm_num)
  have hψpairder (z : SeqL2) :
      fderiv ℝ (fun z' : SeqL2 × ℝ => pd f j z'.1) (z, 0) =
        (fderiv ℝ (pd f j) z).comp (ContinuousLinearMap.fst ℝ SeqL2 ℝ) := by
    have hdif : Differentiable ℝ (pd f j) := hψcd.differentiable (by norm_num)
    exact ((hdif z).hasFDerivAt.comp (z, 0)
      (hasFDerivAt_fst : HasFDerivAt (fun q : SeqL2 × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ SeqL2 ℝ) (z, 0))).fderiv
  have hψpd : ∀ k z,
      fderiv ℝ (fun z' : SeqL2 × ℝ => pd f j z'.1) (z, 0)
          (s45_e1 k (1 : ℝ), 0) = pd (pd f j) k z := by
    intro k z
    rw [hψpairder z]
    rfl
  have hsecond : ∀ z : SeqL2,
      fderiv ℝ (fun z' : SeqL2 × ℝ => pd f j z'.1) (z, 0) (0, 1) = 0 := by
    intro z
    rw [hψpairder z]
    change (fderiv ℝ (pd f j) z) (ContinuousLinearMap.fst ℝ SeqL2 ℝ (0, 1)) = 0
    simp
  let b0 : Euc p.d → ℝ := fun _ => 0
  have hb0mem : MemCb (fp81s21_J1 p.d) b0 :=
    (HRS.MS.Tc5.tc5_cb_const _ _).1
  let Ψ : SeqL2 × ℝ → ℝ := fun z => pd f j z.1
  have hΨ : ContDiff ℝ 1 Ψ := hψcd.comp contDiff_fst
  have hformula := S99.s99_fderivF_apply hN1 hJ hφ hb0mem (ν := ν) hΨ X
    (fun i => gradient (F.χ j) (X i))
  have hNpos : 0 < N := by omega
  have hpair0 : HRS.Whole.pair ν b0 = 0 := by
    simp [HRS.Whole.pair, b0]
  have hemp0 : HRS.Whole.pair (HRS.Whole.empirical X) b0 = 0 := by
    rw [HRS.Whole.pair_empirical hNpos]
    simp [HRS.Whole.pair, b0]
  have hWformula : S99.Zq N φ b0 ν X = (W X, 0) := by
    simp [S99.Zq, b0, W, S45.s45_Yi, hpair0, hemp0]
  rw [hWformula] at hformula
  have hleft : fderiv ℝ (fun Y : EucConfig p.d N => Ψ (S99.Zq N φ b0 ν Y)) X
      (fun i => gradient (F.χ j) (X i)) =
      fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X
        (fun i => gradient (F.χ j) (X i)) := rfl
  rw [hleft] at hformula
  rw [hformula]
  simp only [Ψ, hsecond, add_zero]
  simp_rw [hψpd, S99.s99_L_chi hN1 X]
  simp [b0, gradient_fun_const]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ac_rfl

/-- One term of the response-gradient series under the actual initial law. -/
def fp81s21_initial_wF_integrand
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ)
    (f : SeqL2 → ℝ) (N : ℕ) (j k : ℕ) (X : EucConfig p.d N) : ℝ :=
  HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
    pd (pd f j) k (featureVec φ (r26t3_marg R N) X)

/-- The bounded response-gradient series can be integrated termwise under the initial law. -/
theorem fp81s21_initial_wF_integrand_bound
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (hγ : 0 < p.γ) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 1 ≤ N) (j k : ℕ) :
    ∀ X : EucConfig p.d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
        pd (pd f j) k (featureVec φ (r26t3_marg R N) X)| ≤
        (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
          (p.γ⁻¹ * F.K)) *
            (cbNorm (fp81s21_J1 p.d) (φ j) * cbNorm (fp81s21_J1 p.d) (φ k)) := by
  intro X
  have hwcb := fp81s21_initial_wF_cb hφ.1 F hγ j k
  have hwsup : ∀ x, |InitialFamData.wF F j k x| ≤
      cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j k) := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hwcb.1 x
    rwa [Real.norm_eq_abs] at h
  have hpair := s45_abs_pair_empirical_le hN hwsup X
  have hpd := ((hf.pd j).pd k).abs_le (featureVec φ (r26t3_marg R N) X)
  have hcbnonneg := HRS.MS.Tc5.tc5_cb_nonneg (fp81s21_k0 p.d)
    (InitialFamData.wF F j k)
  rw [abs_mul]
  calc |HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k)| *
        |pd (pd f j) k (featureVec φ (r26t3_marg R N) X)|
      ≤ cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j k) * 1 :=
        mul_le_mul hpair hpd (abs_nonneg _) hcbnonneg
    _ = cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j k) := by rw [mul_one]
    _ ≤ (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j))) *
          cbNorm (fp81s21_J1 p.d) (φ k) := hwcb.2
    _ = _ := by ac_rfl

theorem fp81s21_initial_wF_measurable
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (hγ : 0 < p.γ) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (hP : IsProbabilityMeasure (r26t3_Q R N)) (j : ℕ) :
    ∀ k, AEStronglyMeasurable
      (fun X : EucConfig p.d N => fp81s21_initial_wF_integrand F f N j k X)
      (r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  letI : IsProbabilityMeasure (r26t3_Q R N) := hP
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ (r26t3_marg R N) X
  have hWc : Continuous W :=
    (S99.s99_W_contDiff hN1 (by unfold fp81s21_J1; omega) hφ).continuous
  intro k
  have hm : Measurable (fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
        pd (pd f j) k (featureVec φ (r26t3_marg R N) X)) :=
    (s45_measurable_pair_empirical hN1
      ((fp81s21_initial_wF_cb hφ.1 F hγ j k).1.1.continuous.measurable)).mul
        (((s99_pdpd_cont hf j k).comp hWc).measurable)
  exact hm.aestronglyMeasurable

/-- The initial pair-energy identity applied to one coordinate Stein test. -/
theorem fp81s21_initial_pairEnergy_test
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) -
        HRS.Whole.pair (r26t3_marg R N) (φ j)) *
          pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
      (p.γ * N)⁻¹ * ∫ X,
        fderiv ℝ (fun Y : EucConfig p.d N => pd f j
          (featureVec φ (r26t3_marg R N) Y)) X
            (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) -
      ∫ X, (HRS.Whole.pairEnergy
        (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
        ∫ Y, HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
            ∂(r26t3_Q R N)) * pd f j
              (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  obtain ⟨htest, htestB, hDF⟩ := fp81s21_initial_testData E hφ hf hN j
  have hφ1 : MemCb 1 (φ j) :=
    (HRS.MS.Tc5.tc5_cb_mono (m := 1) (J := fp81s21_J1 p.d)
      (by unfold fp81s21_J1; omega) (hφ.1 j)).1
  exact initial_stein_pairEnergy E hγ hN (F.feat hγ j) hφ1 htest
    (BF := 1) htestB (DF := Real.sqrt N * ∑' k, cbNorm (fp81s21_J1 p.d) (φ k)) hDF

theorem fp81s21_initial_pair_wF_raw
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 1 ≤ N)
    (hγ : 0 < p.γ) {φ : ℕ → Euc p.d → ℝ}
    (F : InitialFamData R φ) (j k : ℕ) (X : EucConfig p.d N) :
    HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) =
      p.γ * HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) := by
  have hpw := fp81s21_initial_pair_wF hN F j k X
  calc
    _ = 1 * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) := by rw [one_mul]
    _ = (p.γ * p.γ⁻¹) * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) := by
          rw [mul_inv_cancel₀ hγ.ne', one_mul]
    _ = p.γ * (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫)) := by rw [mul_assoc]
    _ = p.γ * HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) := by
          rw [← hpw]

theorem fp81s21_initial_wF_series
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 1 ≤ N)
    (hγ : 0 < p.γ) {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ)
    {f : SeqL2 → ℝ} (hf : SteinCl f) (j : ℕ) :
    ∀ X : EucConfig p.d N,
      ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X) =
        p.γ * ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F j k) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X) := by
  intro X
  calc
    _ = ∑' k, p.γ * (HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F j k) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X)) := by
          apply tsum_congr
          intro k
          rw [fp81s21_initial_pair_wF_raw hN hγ F j k X]
          ac_rfl
    _ = _ := by rw [tsum_mul_left]

/-- Pointwise normalized derivative identity for the initial response family. -/
theorem fp81s21_initial_derivative_pointwise
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∀ X : EucConfig p.d N,
      (Real.sqrt N * (p.γ * N)⁻¹) *
        fderiv ℝ (fun Y : EucConfig p.d N => pd f j
          (featureVec φ (r26t3_marg R N) Y)) X
            (fun i => gradient (F.χ j) (X i)) =
      ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
        (InitialFamData.wF F j k) * pd (pd f j) k
          (featureVec φ (r26t3_marg R N) X) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hN0.le
  have hderiv := fp81s21_initial_test_deriv E hφ F hf hN j
  have hseries := fp81s21_initial_wF_series hN1 hγ F hf j
  intro X
  rw [hderiv X]
  have hcoef : (Real.sqrt N * (p.γ * N)⁻¹) * Real.sqrt N = p.γ⁻¹ := by
    calc
      (Real.sqrt N * (p.γ * N)⁻¹) * Real.sqrt N =
          (Real.sqrt N * Real.sqrt N) * (p.γ * N)⁻¹ := by ac_rfl
      _ = (N : ℝ) * (p.γ * N)⁻¹ := by rw [hsq]
      _ = p.γ⁻¹ := by field_simp [hγ.ne', hN0.ne']
  calc
    (Real.sqrt N * (p.γ * N)⁻¹) *
        (Real.sqrt N * ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X)) =
        ((Real.sqrt N * (p.γ * N)⁻¹) * Real.sqrt N) *
          ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫) *
              pd (pd f j) k (featureVec φ (r26t3_marg R N) X) := by ac_rfl
    _ = p.γ⁻¹ * (p.γ * ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F j k) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X)) := by
          rw [hcoef, hseries X]
    _ = (p.γ⁻¹ * p.γ) * ∑' k, HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F j k) *
            pd (pd f j) k (featureVec φ (r26t3_marg R N) X) := by ac_rfl
    _ = _ := by rw [inv_mul_cancel₀ hγ.ne', one_mul]

/-- The nonthermal response integrands are uniformly summable under the initial law. -/
theorem fp81s21_initial_wF_integral_tsum
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∑' k, ∫ X, fp81s21_initial_wF_integrand F f N j k X ∂(r26t3_Q R N) =
      ∫ X, ∑' k, fp81s21_initial_wF_integrand F f N j k X ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  let g : ℕ → EucConfig p.d N → ℝ := fun k X =>
    fp81s21_initial_wF_integrand F f N j k X
  let b : ℕ → ℝ := fun k => cbNorm (fp81s21_J1 p.d) (φ k)
  let C : ℝ := (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
    (p.γ⁻¹ * F.K)) * b j
  let M : ℕ → ℝ := fun k =>
    C * b k
  have hMs : Summable M := hφ.2.mul_left C
  have hmeas := fp81s21_initial_wF_measurable hγ hφ F hf hN hP j
  have hgt : ∀ k, AEStronglyMeasurable (g k) (r26t3_Q R N) := hmeas
  have hbound : ∀ k X, |g k X| ≤ M k := by
    intro k X
    calc
      |g k X| ≤ (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
          (p.γ⁻¹ * F.K)) * (b j * b k) :=
        fp81s21_initial_wF_integrand_bound hγ hφ F hf hN1 j k X
      _ = M k := by dsimp [M, C, b]; ac_rfl
  change (∑' k, ∫ X, g k X ∂(r26t3_Q R N)) =
    ∫ X, ∑' k, g k X ∂(r26t3_Q R N)
  exact @fp81s21_integral_tsum ℕ (EucConfig p.d N)
    (inferInstance : Countable ℕ) (inferInstance : MeasurableSpace (EucConfig p.d N))
    (r26t3_Q R N) hP g M hMs hgt hbound

/-- Integrate the directional derivative series from the nonthermal coordinate test. -/
theorem fp81s21_initial_derivative_integral
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    Real.sqrt N * ((p.γ * N)⁻¹ *
      ∫ X, fderiv ℝ (fun Y : EucConfig p.d N => pd f j
        (featureVec φ (r26t3_marg R N) Y)) X
          (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N)) =
    ∑' k, ∫ X, fp81s21_initial_wF_integrand F f N j k X ∂(r26t3_Q R N) := by
  let ν := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  let g : ℕ → EucConfig p.d N → ℝ := fun k X =>
    fp81s21_initial_wF_integrand F f N j k X
  have hscaled := fp81s21_initial_derivative_pointwise E hγ hφ F hf hN j
  have hsumInt := fp81s21_initial_wF_integral_tsum E hγ hφ F hf hN j
  calc
    Real.sqrt N * ((p.γ * N)⁻¹ *
        ∫ X, fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X
          (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N)) =
        (Real.sqrt N * (p.γ * N)⁻¹) *
          ∫ X, fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X
            (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) := by ac_rfl
    _ = ∫ X, (Real.sqrt N * (p.γ * N)⁻¹) *
          fderiv ℝ (fun Y : EucConfig p.d N => pd f j (W Y)) X
            (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) := by
          rw [← integral_const_mul]
    _ = ∫ X, ∑' k, g k X ∂(r26t3_Q R N) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hscaled
    _ = ∑' k, ∫ X, g k X ∂(r26t3_Q R N) := hsumInt.symm

/-- The nonthermal coordinate identity at the actual initial preparation law. The `Bq` term
uses the corrector gradient `∇χ_j = γ v_j`; the empirical response observable is
`γ⁻¹⟨∇χ_j, ∇φ_k⟩`. -/
theorem fp81s21_initial_coord_identity
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {f : SeqL2 → ℝ} (hf : SteinCl f)
    {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    ∫ X, SeqL2.coord (featureVec φ (r26t3_marg R N) X) j *
        pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
      -(∫ X, (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) *
          pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) +
      ∑' k, ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
          pd (pd f j) k (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hN0.le
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let ν := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  have hI := fp81s21_initial_pairEnergy_test E hγ hφ F hf hN j
  have hcoord : ∀ X : EucConfig p.d N,
      SeqL2.coord (W X) j = s45_Yi N (φ j) (HRS.Whole.pair ν (φ j)) X := fun X =>
    s45_coord_ofSeq (s45_feature_memℓp hN1 hφ X) j
  let g : ℕ → EucConfig p.d N → ℝ := fun k X =>
    fp81s21_initial_wF_integrand F f N j k X
  have hderivIntegral := fp81s21_initial_derivative_integral E hγ hφ F hf hN j
  have henergy : ∀ X : EucConfig p.d N,
      fp81s21_initialBq R (F.χ j) N X / Real.sqrt N =
        Real.sqrt N * (HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
          ∫ Y, HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
              ∂(r26t3_Q R N)) := by
    intro X
    have hsqrt : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
    unfold fp81s21_initialBq
    rw [div_eq_iff hsqrt]
    have hsqr : (Real.sqrt N) ^ 2 = (N : ℝ) := by nlinarith [hsq]
    calc
      (N : ℝ) * (HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
          ∫ Y, HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
              ∂(r26t3_Q R N)) =
          (Real.sqrt N * Real.sqrt N) * (HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
            ∫ Y, HRS.Whole.pairEnergy
              (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
              ∂(r26t3_Q R N)) := by rw [hsq]
      _ = Real.sqrt N * (HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
            ∫ Y, HRS.Whole.pairEnergy
              (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
                ∂(r26t3_Q R N)) * Real.sqrt N := by ac_rfl
  have henergyIntegral :
      Real.sqrt N * ∫ X, (HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
          ∫ Y, HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
              ∂(r26t3_Q R N)) * pd f j (W X) ∂(r26t3_Q R N) =
        ∫ X, (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) *
          pd f j (W X) ∂(r26t3_Q R N) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    calc
      Real.sqrt N * ((HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
          ∫ Y, HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
              ∂(r26t3_Q R N)) * pd f j (W X)) =
          (Real.sqrt N * (HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
            ∫ Y, HRS.Whole.pairEnergy
              (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
                ∂(r26t3_Q R N))) * pd f j (W X) := by ac_rfl
      _ = (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) * pd f j (W X) := by
          rw [← henergy X]
  have hleft :
      ∫ X, SeqL2.coord (featureVec φ (r26t3_marg R N) X) j *
          pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
        Real.sqrt N * ∫ X,
          (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) -
            HRS.Whole.pair (r26t3_marg R N) (φ j)) *
            pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
    have hcoord' : ∀ X : EucConfig p.d N, SeqL2.coord
        (featureVec φ (r26t3_marg R N) X) j =
        Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) -
          HRS.Whole.pair (r26t3_marg R N) (φ j)) := by
      intro X
      rw [hcoord X, S45.s45_Yi]
    simp_rw [hcoord']
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    ac_rfl
  calc
    ∫ X, SeqL2.coord (W X) j * pd f j (W X) ∂(r26t3_Q R N) =
        Real.sqrt N * ((p.γ * N)⁻¹ *
          ∫ X, fderiv ℝ (fun Y : EucConfig p.d N =>
            pd f j (featureVec φ (r26t3_marg R N) Y)) X
            (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) -
          ∫ X, (HRS.Whole.pairEnergy
            (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) X (r26t3_mu R 0) -
            ∫ Y, HRS.Whole.pairEnergy
              (HRS.Whole.commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
                ∂(r26t3_Q R N)) *
              pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) := by
      rw [hleft, hI]
    _ = -(∫ X, (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) *
          pd f j (W X) ∂(r26t3_Q R N)) +
        ∑' k, ∫ X, g k X ∂(r26t3_Q R N) := by
      rw [mul_sub, hderivIntegral, henergyIntegral]
      exact (sub_eq_add_neg _ _).trans (add_comm _ _)
    _ = -(∫ X, (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) *
          pd f j (W X) ∂(r26t3_Q R N)) +
        ∑' k, ∫ X, HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F j k) * pd (pd f j) k (W X) ∂(r26t3_Q R N) := by
      rfl
    _ = _ := by rfl
end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_integral_tsum
#print axioms HRS.Fp81.S21.fp81s21_initial_testData
#print axioms HRS.Fp81.S21.fp81s21_initial_test_deriv
#print axioms HRS.Fp81.S21.fp81s21_initial_wF_integrand_bound
#print axioms HRS.Fp81.S21.fp81s21_initial_wF_measurable
#print axioms HRS.Fp81.S21.fp81s21_initial_pairEnergy_test
#print axioms HRS.Fp81.S21.fp81s21_initial_pair_wF_raw
#print axioms HRS.Fp81.S21.fp81s21_initial_wF_series
#print axioms HRS.Fp81.S21.fp81s21_initial_derivative_pointwise
#print axioms HRS.Fp81.S21.fp81s21_initial_wF_integral_tsum
#print axioms HRS.Fp81.S21.fp81s21_initial_derivative_integral
#print axioms HRS.Fp81.S21.fp81s21_initial_coord_identity
