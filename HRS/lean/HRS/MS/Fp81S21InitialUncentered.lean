import HRS.MS.Fp81S21InitialFam2
import HRS.MS.Fp81S21InitialStein3
import HRS.MS.R2SeAux5

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- The physical commutator coefficient in the uncentered response identity. The velocity is
the compatible one supplied by `InitialFamData`, namely `γ⁻¹ ∇χ`. -/
def fp81s21_initial_Bcoord {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (N j : ℕ)
    (X : EucConfig p.d N) : ℝ :=
  (N : ℝ) * (pairEnergy
      (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
      X (r26t3_mu R 0) -
    ∫ Y, pairEnergy
      (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
      Y (r26t3_mu R 0) ∂(r26t3_Q R N))

/-!
Thermal source contract: `S99.s99_E1_plain` (R2SeAux9:81), obtained from `s99_E1`
(R2SeAux6:34), states the feature-coordinate response identity. Its `S45.s45_Rp` term is
converted in `s99_sqrt_Rp` (R2SeAux7:34) to the centered pair energy, and `S99.Bq`
(R2SeAux7:29) is `N` times that centered energy. Before the coefficient is split into its
mean and centered fluctuation, the response identity is therefore the identity exported below.
The S99 proof uses the thermal `S46.s46_stein_id`; this port instead invokes the actual-law
`initial_stein_pairEnergy` and keeps its explicit mean subtraction.
-/

/-- The uncentered response identity at the actual initial preparation law. In particular, the
coefficient of each feature derivative is the empirical pairing itself; no marginal mean has
been subtracted from it. -/
theorem fp81s21_initial_uncentered_response
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (j : ℕ)
    {f : SeqL2 → ℝ} (hf : Bd 1 f) :
    ∫ X, s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X *
        f (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
      (∑' k, ∫ X,
        HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
          pd f k (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
      (p.γ / Real.sqrt N) *
        ∫ X, fp81s21_initial_Bcoord F N j X *
          f (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hJ : 1 ≤ fp81s21_J1 p.d := by
    unfold fp81s21_J1
    omega
  have hJone : (1 : ℕ) ≤ fp81s21_J1 p.d := hJ
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := s99_nu_prob hN1
  have hφ1 : MemCb 1 (φ j) :=
    (HRS.MS.Tc5.tc5_cb_mono (m := 1) (J := fp81s21_J1 p.d) hJone (hφ.1 j)).1
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ (r26t3_marg R N) X
  let g : EucConfig p.d N → ℝ := fun X => f (W X)
  have hW : ContDiff ℝ 1 W := s99_W_contDiff hN1 hJ hφ
  have hgc : ContDiff ℝ 1 g := hf.1.comp hW
  have hgBound : ∀ X, |g X| ≤ 1 := by
    intro X
    have h := hf.2 0 (by omega) (W X)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h
  have hcb : Summable (fun k : ℕ => cbNorm (fp81s21_J1 p.d) (φ k)) := hφ.2
  set Csum : ℝ := ∑' k, Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)
  have hCsum0 : 0 ≤ Csum := tsum_nonneg fun k =>
    mul_nonneg (Real.sqrt_nonneg _) (HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hCLMsum : ∀ X : EucConfig p.d N,
      Summable (fun k : ℕ => (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) := by
    intro X
    exact Summable.of_norm_bounded (hcb.mul_left (Real.sqrt N))
      (fun k => s99_Wterm_fderiv_norm hN1 hJ (hφ.1) k X)
  have hDFg : ∀ X, ‖fderiv ℝ g X‖ ≤ Csum := by
    intro X
    have hchain := (hf.1.differentiable one_ne_zero (W X)).hasFDerivAt.comp X
      (s99_W_hasFDerivAt (ν := r26t3_marg R N) hN1 hJ hφ X)
    refine ContinuousLinearMap.opNorm_le_bound _ hCsum0 fun u => ?_
    change ‖fderiv ℝ (f ∘ W) X u‖ ≤ Csum * ‖u‖
    rw [hchain.fderiv]
    change ‖fderiv ℝ f (W X)
        ((∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u)‖ ≤
      Csum * ‖u‖
    have hEval := (hCLMsum X).hasSum.mapL
      (ContinuousLinearMap.apply ℝ SeqL2 u)
    have hEvalEq :
        (∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)) u) =
          (∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u := by
      simpa using hEval.tsum_eq
    have hsum : HasSum
        (fun k : ℕ => (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖)
        (∑' k, (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖) :=
      by
        simpa only [tsum_mul_right] using
          ((hcb.mul_left (Real.sqrt N)).hasSum).mul_right ‖u‖
    have hsumEq :
        (∑' k, (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖) =
          Csum * ‖u‖ := by
      rw [tsum_mul_right]
    have hterm : ∀ k, ‖(s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)) u‖ ≤
        (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖ := by
      intro k
      calc ‖(s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)) u‖ ≤
            ‖(s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))‖ * ‖u‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖ :=
              mul_le_mul_of_nonneg_right
                (s99_Wterm_fderiv_norm hN1 hJ (hφ.1) k X) (norm_nonneg _)
    have hsumV :
        ‖(∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u‖ ≤
          Csum * ‖u‖ := by
      calc ‖(∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u‖ =
            ‖∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)) u‖ := by
              rw [hEvalEq]
        _ ≤ ∑' k, (Real.sqrt N * cbNorm (fp81s21_J1 p.d) (φ k)) * ‖u‖ :=
              tsum_of_norm_bounded hsum hterm
        _ = Csum * ‖u‖ := hsumEq
    calc ‖fderiv ℝ f (W X)
          ((∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u)‖ ≤
          ‖fderiv ℝ f (W X)‖ *
            ‖(∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))) u‖ :=
            (fderiv ℝ f (W X)).le_opNorm _
      _ ≤ 1 * (Csum * ‖u‖) := by
            have hfd : ‖fderiv ℝ f (W X)‖ ≤ 1 := by
              rw [← norm_iteratedFDeriv_one]
              exact hf.2 1 (by omega) (W X)
            exact mul_le_mul hfd hsumV (norm_nonneg _) zero_le_one
      _ = Csum * ‖u‖ := one_mul _
  have hfeat : S47.S47Feat p.d p.s (R.ρ 0) p.γ (φ j) (F.χ j)
      (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) := F.feat hγ j
  have hDF : ∀ X, ‖fderiv ℝ g X‖ ≤ Csum := hDFg
  have hstein := initial_stein_pairEnergy E hγ hN hfeat hφ1 hgc
    (BF := 1) hgBound (DF := Csum) hDF
  have hcompDeriv : ∀ X,
      fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) =
        ∑' k, (Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫)) *
          fderiv ℝ f (W X) (s45_e1 k (1 : ℝ)) := by
    intro X
    have hchain := (hf.1.differentiable one_ne_zero (W X)).hasFDerivAt.comp X
      (s99_W_hasFDerivAt (ν := r26t3_marg R N) hN1 hJ hφ X)
    change fderiv ℝ (f ∘ W) X (fun i => gradient (F.χ j) (X i)) = _
    rw [hchain.fderiv]
    change fderiv ℝ f (W X)
        ((∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)))
          (fun i => gradient (F.χ j) (X i))) = _
    have hEval := (hCLMsum X).hasSum.mapL
      (ContinuousLinearMap.apply ℝ SeqL2 (fun i => gradient (F.χ j) (X i)))
    have hEval' := hEval.mapL (fderiv ℝ f (W X))
    have hEvalEq' :
        (∑' k, fderiv ℝ f (W X)
          ((s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ))
            (fun i => gradient (F.χ j) (X i)))) =
          fderiv ℝ f (W X)
            ((∑' k, (s45_L N (φ k) X).smulRight (s45_e1 k (1 : ℝ)))
              (fun i => gradient (F.χ j) (X i))) := by
      simpa using hEval'.tsum_eq
    rw [← hEvalEq']
    refine tsum_congr fun k => ?_
    simp only [ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
    rw [s99_L_chi hN1 X]
  have hwfb : ∀ k x, |InitialFamData.wF F j k x| ≤
      p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
        cbNorm (fp81s21_J1 p.d) (φ k) := by
    intro k x
    unfold InitialFamData.wF
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    have h := abs_real_inner_le_norm (gradient (F.χ j) x) (gradient (φ k) x)
    have hj := F.deriv j x 0 (Nat.zero_le _)
    have hjgrad : ‖gradient (F.χ j) x‖ ≤
        F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
      rw [s45_norm_gradient, ← norm_iteratedFDeriv_one]
      exact hj
    have hk := s45_cb_deriv_le (by exact_mod_cast hJ) (hφ.1 k) x
    have hkgrad : ‖gradient (φ k) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ k) := by
      rw [s45_norm_gradient]
      exact hk
    calc p.γ⁻¹ * |⟪gradient (F.χ j) x, gradient (φ k) x⟫| ≤
          p.γ⁻¹ * (‖gradient (F.χ j) x‖ * ‖gradient (φ k) x‖) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.2 hγ.le)
      _ ≤ p.γ⁻¹ * ((F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
            cbNorm (fp81s21_J1 p.d) (φ k)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hjgrad hkgrad (norm_nonneg _)
                (mul_nonneg F.hK (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
              (inv_nonneg.2 hγ.le)
      _ = _ := by ring
  let G : ℕ → EucConfig p.d N → ℝ := fun k X =>
    HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) *
      pd f k (W X)
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k
    have hφk : ContDiff ℝ 1 (φ k) := (hφ.1 k).1.of_le (by exact_mod_cast hJ)
    have hχc : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient hfeat.smooth
    have hwc : Continuous (InitialFamData.wF F j k) := by
      unfold InitialFamData.wF
      exact continuous_const.mul (hχc.continuous.inner (s45_gradient_continuous hφk))
    have hpair : Measurable (fun X : EucConfig p.d N =>
        HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k)) :=
      s45_measurable_pair_empirical hN1 hwc.measurable
    have hfdc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv one_ne_zero
    have hpdc : Continuous (fun z : SeqL2 => pd f k z) := by
      unfold pd
      exact (hfdc.clm_apply continuous_const)
    exact hpair.mul (hpdc.comp hW.continuous).measurable
  have hGbound : ∀ k X, ‖G k X‖ ≤
      (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j))) *
        cbNorm (fp81s21_J1 p.d) (φ k) := by
    intro k X
    rw [Real.norm_eq_abs]
    unfold G pd
    rw [abs_mul]
    have hpair := s45_abs_pair_empirical_le hN1 (fun x => hwfb k x) X
    have hpd : |fderiv ℝ f (W X) (s45_e1 k (1 : ℝ))| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ f (W X) (s45_e1 k (1 : ℝ))‖ ≤
            ‖fderiv ℝ f (W X)‖ * ‖s45_e1 k (1 : ℝ)‖ :=
              (fderiv ℝ f (W X)).le_opNorm _
        _ ≤ 1 := by
              rw [s99_e1_norm, mul_one, ← norm_iteratedFDeriv_one]
              exact hf.2 1 (by omega) (W X)
    have hnon : 0 ≤ p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) := by
      exact mul_nonneg (inv_nonneg.mpr hγ.le)
        (mul_nonneg F.hK (HRS.MS.Tc5.tc5_cb_nonneg _ _))
    have hupper : 0 ≤ (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j))) *
        cbNorm (fp81s21_J1 p.d) (φ k) :=
      mul_nonneg hnon (HRS.MS.Tc5.tc5_cb_nonneg _ _)
    calc |HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k)| *
          |fderiv ℝ f (W X) (s45_e1 k (1 : ℝ))| ≤
          (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
            cbNorm (fp81s21_J1 p.d) (φ k)) * 1 :=
            mul_le_mul hpair hpd (abs_nonneg _) hupper
      _ = _ := by ring
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hGint : ∀ k, Integrable (G k) (r26t3_Q R N) := by
    intro k
    exact Integrable.of_bound (hGmeas k).aestronglyMeasurable
      (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
        cbNorm (fp81s21_J1 p.d) (φ k))
      (Filter.Eventually.of_forall fun X => hGbound k X)
  have hsumG : Summable (fun k => ∫ X, ‖G k X‖ ∂(r26t3_Q R N)) := by
    exact Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun X => norm_nonneg _)
      (fun k => by
        calc ∫ X, ‖G k X‖ ∂(r26t3_Q R N) ≤
              ∫ X, (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j))) *
                cbNorm (fp81s21_J1 p.d) (φ k) ∂(r26t3_Q R N) :=
              integral_mono (hGint k).norm (integrable_const _) (fun X => hGbound k X)
          _ = (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j))) *
                cbNorm (fp81s21_J1 p.d) (φ k) := by simp)
      (hcb.mul_left
        (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j))))
  have hGtsum := integral_tsum_of_summable_integral_norm hGint hsumG
  have hderInt :
      (Real.sqrt N * (p.γ * (N : ℝ))⁻¹) *
        ∫ X, fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) =
      ∑' k, ∫ X, G k X ∂(r26t3_Q R N) := by
    have hcoeff : Real.sqrt N * (p.γ * (N : ℝ))⁻¹ * Real.sqrt N = p.γ⁻¹ := by
      field_simp [hγ.ne', hN0.ne']
      rw [Real.sq_sqrt hN0.le]
    have hpairScale (c : ℝ) (q : Euc p.d → ℝ) (X : EucConfig p.d N) :
        HRS.Whole.pair (HRS.Whole.empirical X) (fun x => c * q x) =
          c * HRS.Whole.pair (HRS.Whole.empirical X) q := by
      have hNpos : 0 < N := by omega
      rw [HRS.Whole.pair_empirical hNpos, HRS.Whole.pair_empirical hNpos,
        ← Finset.mul_sum]
      ring
    have hpoint : ∀ X,
        (Real.sqrt N * (p.γ * (N : ℝ))⁻¹) *
            fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) =
          ∑' k, G k X := by
      intro X
      rw [hcompDeriv X]
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      change Real.sqrt N * (p.γ * (N : ℝ))⁻¹ *
          ((Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient (F.χ j) x, gradient (φ k) x⟫)) *
            fderiv ℝ f (W X) (s45_e1 k (1 : ℝ))) =
        HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => p.γ⁻¹ * ⟪gradient (F.χ j) x, gradient (φ k) x⟫) *
          fderiv ℝ f (W X) (s45_e1 k (1 : ℝ))
      rw [hpairScale]
      rw [← hcoeff]
      ring
    calc (Real.sqrt N * (p.γ * (N : ℝ))⁻¹) *
          ∫ X, fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) =
        ∫ X, (Real.sqrt N * (p.γ * (N : ℝ))⁻¹) *
          fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) := by
            rw [integral_const_mul]
      _ = ∫ X, ∑' k, G k X ∂(r26t3_Q R N) := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            exact hpoint
      _ = ∑' k, ∫ X, G k X ∂(r26t3_Q R N) := hGtsum.symm
  have hkernel :
      commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x) =
        fun x y => p.γ⁻¹ * commutatorKernel p.d p.s (gradient (F.χ j)) x y := by
    funext x y
    simp only [commutatorKernel]
    calc ⟪p.γ⁻¹ • gradient (F.χ j) x - p.γ⁻¹ • gradient (F.χ j) y,
          rieszKernelGrad p.d p.s (x - y)⟫ =
        ⟪p.γ⁻¹ • (gradient (F.χ j) x - gradient (F.χ j) y),
          rieszKernelGrad p.d p.s (x - y)⟫ := by rw [← smul_sub]
      _ = p.γ⁻¹ * ⟪gradient (F.χ j) x - gradient (F.χ j) y,
          rieszKernelGrad p.d p.s (x - y)⟫ := by rw [real_inner_smul_left]
  have henergy : ∀ X : EucConfig p.d N,
      pairEnergy
          (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
          X (r26t3_mu R 0) -
        ∫ Y, pairEnergy
          (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
          Y (r26t3_mu R 0) ∂(r26t3_Q R N) =
      p.γ⁻¹ * (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
          X (r26t3_mu R 0) -
        ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
          Y (r26t3_mu R 0) ∂(r26t3_Q R N)) := by
    intro X
    have hpY : ∀ Y : EucConfig p.d N,
        pairEnergy
          (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
          Y (r26t3_mu R 0) = p.γ⁻¹ *
            pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0) := by
      intro Y
      rw [hkernel]
      unfold pairEnergy
      simp only [integral_const_mul, ← Finset.mul_sum]
      ring
    rw [hpY X]
    have hinter :
        (∫ Y, pairEnergy
          (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
          Y (r26t3_mu R 0) ∂(r26t3_Q R N)) =
          p.γ⁻¹ * ∫ Y, pairEnergy
            (commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
            ∂(r26t3_Q R N) := by
      rw [show (fun Y : EucConfig p.d N => pairEnergy
          (commutatorKernel p.d p.s (fun x => p.γ⁻¹ • gradient (F.χ j) x))
          Y (r26t3_mu R 0)) =
        fun Y => p.γ⁻¹ * pairEnergy
          (commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0) from funext hpY,
        integral_const_mul]
    rw [hinter]
    ring
  have hBpoint : ∀ X : EucConfig p.d N,
      (p.γ / Real.sqrt N) * fp81s21_initial_Bcoord F N j X =
        Real.sqrt N * (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
            X (r26t3_mu R 0) -
          ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
            Y (r26t3_mu R 0) ∂(r26t3_Q R N)) := by
    intro X
    rw [fp81s21_initial_Bcoord, henergy X]
    field_simp [hγ.ne', hsqrt]
    rw [Real.sq_sqrt hN0.le]
  have hsteinScaled :
    ∫ X, s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X * g X ∂(r26t3_Q R N) =
      Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ *
        ∫ X, fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) -
        ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j))) X
              (r26t3_mu R 0) -
            ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j))) Y
              (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X ∂(r26t3_Q R N)) := by
    have hleft :
        ∫ X, s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X * g X ∂(r26t3_Q R N) =
          Real.sqrt N * ∫ X,
            (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) - HRS.Whole.pair (r26t3_marg R N) (φ j)) * g X
            ∂(r26t3_Q R N) := by
      rw [← integral_const_mul]
      congr 1
      funext X
      simp [s45_Yi, g]
      ring
    rw [hleft, hstein]
  calc ∫ X, s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X *
        f (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
      ∫ X, s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X * g X ∂(r26t3_Q R N) := by
        rfl
    _ = (∑' k, ∫ X, G k X ∂(r26t3_Q R N)) -
        (p.γ / Real.sqrt N) *
          ∫ X, fp81s21_initial_Bcoord F N j X * g X ∂(r26t3_Q R N) := by
        rw [hsteinScaled, mul_sub]
        have hderGrouped :
            Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ *
              ∫ X, fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N)) =
              ∑' k, ∫ X, G k X ∂(r26t3_Q R N) := by
          calc
            _ = Real.sqrt N * (p.γ * (N : ℝ))⁻¹ *
                ∫ X, fderiv ℝ g X (fun i => gradient (F.χ j) (X i)) ∂(r26t3_Q R N) := by ring
            _ = _ := hderInt
        rw [hderGrouped]
        have hBint :
            (p.γ / Real.sqrt N) *
                ∫ X, fp81s21_initial_Bcoord F N j X * g X ∂(r26t3_Q R N) =
              Real.sqrt N *
                ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    X (r26t3_mu R 0) -
                  ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    Y (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X ∂(r26t3_Q R N) := by
          have hpoint : ∀ X,
              (p.γ / Real.sqrt N) * fp81s21_initial_Bcoord F N j X * g X =
                Real.sqrt N *
                  (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                      X (r26t3_mu R 0) -
                    ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                      Y (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X := by
              intro X
              calc
                _ = ((p.γ / Real.sqrt N) * fp81s21_initial_Bcoord F N j X) * g X := by ring
                _ = _ := by rw [hBpoint X]
          calc (p.γ / Real.sqrt N) *
                ∫ X, fp81s21_initial_Bcoord F N j X * g X ∂(r26t3_Q R N) =
              ∫ X, (p.γ / Real.sqrt N) *
                (fp81s21_initial_Bcoord F N j X * g X) ∂(r26t3_Q R N) := by
                  rw [integral_const_mul]
            _ = ∫ X, Real.sqrt N *
                (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    X (r26t3_mu R 0) -
                  ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    Y (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X ∂(r26t3_Q R N) := by
                  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro X
                  calc
                    _ = ((p.γ / Real.sqrt N) * fp81s21_initial_Bcoord F N j X) * g X := by ring
                    _ = _ := hpoint X
            _ = Real.sqrt N *
                ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    X (r26t3_mu R 0) -
                  ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                    Y (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X ∂(r26t3_Q R N) := by
                  calc
                    _ = ∫ X, Real.sqrt N *
                        ((pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                            X (r26t3_mu R 0) -
                          ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j)))
                            Y (r26t3_mu R 0) ∂(r26t3_Q R N)) * g X)
                        ∂(r26t3_Q R N) := by
                          congr 1
                          funext X
                          ring
                    _ = _ := by rw [integral_const_mul]
        rw [hBint]
    _ = _ := by rfl

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_uncentered_response
