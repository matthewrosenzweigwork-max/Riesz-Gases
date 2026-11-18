import HRS.MS.Fp81S21InitialLinear2
import HRS.MS.Fp81S21InitialUncentered4
import HRS.MS.R2SeAux16
import HRS.MS.R2SeAux17

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-!
## SOL31 packet 24a: `Ylin` and the deterministic coefficient rate

Exact thermal `S99.s99_Ylin` contract (`R2SeAux22:50`): given the thermal static context,
a summable `J1` feature family and the matching centered Gaussian, it selects `KL ≥ 0` before
`N`, `w`, and `ψ`; for every `N ≥ 2`, `w ∈ MemCb (k0 d)`, and `ψ ∈ Bd 3`,
`| E[Y_w ψ(W_N)] - ∑' m (∫ w aRep(φ_m) dμ) E_G[pd ψ m] |
 ≤ KL * cbNorm(k0,w) / sqrt N`, where
`Y_w = sqrt N * (pair(empirical,w) - pair(ν_N,w))`.
Its proof uses `s99_chi1`, `s99_E1_plain`, `s99_Bq_bound`, `s99_T_L2/T_L1`, and
`s99_clt`. For the actual law, the corrector, arbitrary-w response, and leading comparison
are already ported; `S47.s47_R_bound` replaces `s99_Bq_bound`, and `S47.s47_T_bound`
replaces `s99_T_L1`. `InitialSteinEnv` supplies the actual reference and static laws.
The coefficient identity below uses generic `S47.s47_cov_identity` and `s47_ibp_mu` with
`InitialFamData.gen`; it does not assume a thermal Euler equation.

Dependency classification: feature differentiation, bounded-integral estimates, and the
summable-series argument are **generic**; `s99_chi1`, `s99_E1_plain`, and `s99_clt` are
**already ported** in the preceding files. `s99_Bq_bound` and `s99_T_L1` are
**thermal-only** and are replaced by the actual-law S47 `R_bound` and `T_bound`; the actual
corrector covariance identity is **already ported** using the generic S47 covariance and
weighted integration-by-parts facts.

Exact thermal `S99.s99_A_rate` contract (`R2SeAux18:31`; `Aterm`, `cc`, and `Alim` are in
`R2SeAux16:68–82`): with the same context and a family `FamData`, it selects `KA ≥ 0`
before `N`, the Stein-class test `f`, and `(j,k)`, and bounds
`|Aterm N f (j,k) - Alim f (j,k)| ≤ KA * b_j * b_k / sqrt N`.
Its dependencies are the arbitrary-observable corrector and plain response, `Ylin`, the
coefficient identity, and the deterministic bias. The product regularity bound and the
derivative-sensitive actual-law biases are already ported (`fp81s21_initial_wF_cb`,
`fp81s21_initial_Cf_bias_s48`, and `fp81s21_initial_marginal_bias_s48`). The latter is the
actual marginal estimate used by the former. The proof below bounds `s48_Q` by the ordinary
`cbNorm` of the same product observable, so the exported rate retains the thermal feature
product envelope.

Dependency classification: the empirical-pairing identity by exchangeability, integral
algebra, and bounded-test estimates are **generic**; `s99_chi1`, `s99_E1_plain`, and `s99_clt`
are **already ported** at the actual initial law in the preceding files, and the actual
`wF` product, covariance identity, and two S48 bias estimates are **already ported**. The
thermal-law covariance identification and `s99_bias` are **thermal-only** and are replaced by
`fp81s21_initial_Cf_eq_wF` and the actual-law marginal/Cf bias estimates. The thermal `T_L1`
and `Bq` bounds enter only through `Ylin`, where `S47.s47_T_bound` and
`S47.s47_R_bound` are already used.
-/

/-- At the actual initial law, covariance with a smooth bounded test equals its pairing with
the response representative of the corrected feature. -/
theorem fp81s21_initial_cov_response_integral
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {w : Euc p.d → ℝ}
    (hw : MemCb (fp81s21_k0 p.d) w) (m : ℕ) :
    HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ (φ m) w =
      ∫ x, w x * r26t3_a R (φ m) x ∂(r26t3_mu R 0) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  have hJ : 1 ≤ fp81s21_k0 p.d := fp81s21_k0_ge_one p.d
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hwc1 : ContDiff ℝ 1 w := hw.1.of_le (by exact_mod_cast hJ)
  have hwbd : ∀ x, |w x| ≤ cbNorm (fp81s21_k0 p.d) w := by
    intro x
    have h := S99.s99_norm_iter_le_cb hw (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ cbNorm (fp81s21_k0 p.d) w := fun x =>
    s45_cb_deriv_le hJ hw x
  have hφm : MemLp (φ m) 2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 m)
  have hfeat := F.feat hγ m
  have hcov := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
    hfeat.smooth hfeat.B1 hfeat.B2 hφm hfeat.r2 hfeat.corr
    hwc1 (Bφ := cbNorm (fp81s21_k0 p.d) w)
      (Dφ := cbNorm (fp81s21_k0 p.d) w) hwbd hDw
  have hibp := S47.s47_ibp_mu E.reference hfeat.smooth hfeat.B1 hfeat.B2
    hwc1 (Bφ := cbNorm (fp81s21_k0 p.d) w)
      (Dφ := cbNorm (fp81s21_k0 p.d) w) hwbd hDw
  have hgen : ∫ x, w x * weightedGen (R.ρ 0) (F.χ m) x
      ∂(HRS.Whole.withDensityReal (R.ρ 0)) =
      p.γ * ∫ x, w x * r26t3_a R (φ m) x
        ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by
    calc
      _ = ∫ x, p.γ * (w x * r26t3_a R (φ m) x) ∂(r26t3_mu R 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change w x * weightedGen (R.ρ 0) (F.χ m) x =
          p.γ * (w x * r26t3_a R (φ m) x)
        rw [F.gen m x]
        ring
      _ = _ := integral_const_mul _ _
  have hgrad :
      ∫ x, ⟪gradient (F.χ m) x, gradient w x⟫
        ∂(HRS.Whole.withDensityReal (R.ρ 0)) =
        ∫ x, w x * weightedGen (R.ρ 0) (F.χ m) x
          ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by
    calc
      _ = ∫ x, ⟪gradient w x, gradient (F.χ m) x⟫ ∂(r26t3_mu R 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact real_inner_comm _ _
      _ = _ := hibp.symm
  change HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
    (HRS.Whole.withDensityReal (R.ρ 0)) p.γ (φ m) w = _
  calc
    _ = p.γ⁻¹ * ∫ x, ⟪gradient (F.χ m) x, gradient w x⟫
        ∂(HRS.Whole.withDensityReal (R.ρ 0)) := hcov
    _ = p.γ⁻¹ * (p.γ * ∫ x, w x * r26t3_a R (φ m) x
        ∂(HRS.Whole.withDensityReal (R.ρ 0))) := by rw [hgrad, hgen]
    _ = ∫ x, w x * r26t3_a R (φ m) x
        ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by
        calc
          _ = (p.γ⁻¹ * p.γ) * ∫ x, w x * r26t3_a R (φ m) x
              ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hγ.ne', one_mul]
    _ = ∫ x, w x * r26t3_a R (φ m) x ∂(r26t3_mu R 0) := rfl

/-- The derivative-sensitive seminorm of a bounded smooth observable is at most a
dimension-dependent multiple of its full bounded norm. -/
theorem fp81s21_s48_Q_le_cb
    {p : Parameters} {μ : Measure (Euc p.d)} [IsProbabilityMeasure μ]
    {w : Euc p.d → ℝ} (hw : MemCb (fp81s21_k0 p.d) w) :
    HRS.MS.S48.s48_Q μ (fp81s21_k0 p.d) w ≤
      ((fp81s21_k0 p.d : ℝ) + 1) * cbNorm (fp81s21_k0 p.d) w := by
  let J : ℕ := fp81s21_k0 p.d
  let B : ℝ := cbNorm J w
  have hJ : 1 ≤ J := by dsimp [J]; exact fp81s21_k0_ge_one p.d
  have hB : 0 ≤ B := HRS.MS.Tc5.tc5_cb_nonneg J w
  have hwbd : ∀ x, |w x| ≤ B := by
    intro x
    have h := S99.s99_norm_iter_le_cb hw (Nat.zero_le _) x
    simpa [J, B, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
  have hwLp : MemLp w 2 μ := HRS.MS.Tc5.tc5_memLp_of_cb hw
  have hcenter : HRS.Whole.l2Norm μ (HRS.Whole.projMean μ w) ≤ B := by
    exact (HRS.Whole.S71.s71_l2Norm_projMean_le hwLp).trans
      (HRS.Whole.S71.s71_l2Norm_le_of_bound hB hwbd)
  have hder : HRS.MS.S48.s48_Dn J w ≤ (J : ℝ) * B := by
    unfold HRS.MS.S48.s48_Dn
    calc
      _ ≤ ∑ j ∈ Finset.range J, B := by
        apply Finset.sum_le_sum
        intro j hj
        apply ciSup_le
        intro x
        have hj' : j < J := Finset.mem_range.mp hj
        exact S99.s99_norm_iter_le_cb hw (by omega) x
      _ = (J : ℝ) * B := by simp
  unfold HRS.MS.S48.s48_Q
  change HRS.Whole.l2Norm μ (HRS.Whole.projMean μ w) +
      HRS.MS.S48.s48_Dn J w ≤ ((J : ℝ) + 1) * B
  nlinarith

/-- Symmetry of the susceptibility covariance at the actual initial reference law. -/
theorem fp81s21_initial_covariance_symmetric
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {f g : Euc p.d → ℝ}
    (hf : MemLp f 2 (r26t3_mu R 0)) (hg : MemLp g 2 (r26t3_mu R 0)) :
    HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f g =
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ g f := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hd1 : 1 ≤ p.d := by have := p.hd; omega
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  obtain ⟨L, hL⟩ := S47.s47_logmoment2 E.reference
  have hM : ∀ x, R.ρ 0 x ≤ E.C := fun x => by
    refine (le_abs_self _).trans ((E.reference.h0 x).trans ?_)
    have he : Real.exp (-E.c * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, E.reference.hc])
    nlinarith [E.reference.C0]
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      IsKData (r26t3_mu R 0) (rieszKernel p.d p.s) K := by
    exact S45.s45_kdata hd1 p.hs0 hsd E.reference.prob hM (L := L)
      (fun _ => by simpa [r26t3_mu] using hL)
  rw [S45.s45_susceptibilityCov_eq hK hγ hf hg,
    S45.s45_susceptibilityCov_eq hK hγ hg hf]
  exact S45.s45_inner_Rr_comm hK hγ.le _ _

/-- The coefficient of the `m`th feature derivative in the arbitrary-observable linear term. -/
def fp81s21_initial_kap {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (w : Euc p.d → ℝ) (φ : ℕ → Euc p.d → ℝ) (m : ℕ) : ℝ :=
  ∫ x, w x * r26t3_a R (φ m) x ∂(r26t3_mu R 0)

/-- The S9.9 linear statistic against a feature-vector test, at the actual initial law. The
constant is chosen before `N`, the arbitrary screened observable, and the test function. -/
theorem fp81s21_initial_Ylin
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (φ i) (φ j))) :
    ∃ KL : ℝ, 0 ≤ KL ∧ ∀ N : ℕ, 2 ≤ N → ∀ {w : Euc p.d → ℝ},
      MemCb (fp81s21_k0 p.d) w → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 3 ψ →
      |(∫ X, s45_Yi N w (HRS.Whole.pair (r26t3_marg R N) w) X *
          ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
        ∑' m, fp81s21_initial_kap (R := R) w φ m *
          ∫ z, S99.pd ψ m z ∂G| ≤
        KL * cbNorm (fp81s21_k0 p.d) w / Real.sqrt N := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  obtain ⟨K₂, hK₂, hcorrect⟩ :=
    fp81s21_initial_orderOne_corrector hδ hδh R hγ
  obtain ⟨KR, hKR, hRbound⟩ :=
    S47.s47_R_bound p.hd p.hs0 hsd E.C E.Cs E.Cs_nonneg
  obtain ⟨KT, hKT, hTbound⟩ :=
    S47.s47_T_bound p.hd p.hs0 hsd E.Cs E.Cs_nonneg
  obtain ⟨Kclt, hKclt, hclt⟩ :=
    fp81s21_initial_clt hδh R hγ hφ hG
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  let Sb : ℝ := ∑' m, b m
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  let KL : ℝ := KR * K₂ + (KT + Kclt) * p.γ⁻¹ * K₂ * Sb
  have hKL : 0 ≤ KL := by positivity
  refine ⟨KL, hKL, fun N hN w hw ψ hψ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hk0 : 1 ≤ fp81s21_k0 p.d := fp81s21_k0_ge_one p.d
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hδN : HRS.deltaN p.d p.s N = 1 / (N : ℝ) := by
    have hmul := HRS.MS.R2Mt.s92_mul_deltaN (d := p.d) (N := N) p.hs hN
    field_simp
    linarith
  have hsqrtδ : Real.sqrt (HRS.deltaN p.d p.s N) = 1 / Real.sqrt N := by
    rw [hδN, Real.sqrt_div (by norm_num), Real.sqrt_one]
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  have hWc : Continuous W := (S99.s99_W_contDiff hN1 hJ hφ).continuous
  have hψWbd : ∀ X, |ψ (W X)| ≤ 1 := fun X => hψ.abs_le _
  have hψWm : Measurable fun X : EucConfig p.d N => ψ (W X) :=
    (hψ.1.continuous.comp hWc).measurable
  let cw : ℝ := cbNorm (fp81s21_k0 p.d) w
  have hcw0 : 0 ≤ cw := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hwbd : ∀ x, |w x| ≤ cw := by
    intro x
    have hh := S99.s99_norm_iter_le_cb hw (Nat.zero_le _) x
    simpa [cw, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have hwm : Measurable w := hw.1.continuous.measurable
  have hwc1 : ContDiff ℝ 1 w := hw.1.of_le (by exact_mod_cast hk0)
  have hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ cw := fun x => s45_cb_deriv_le hk0 hw x
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hwl2 : MemLp w 2 (r26t3_mu R 0) := HRS.MS.Tc5.tc5_memLp_of_cb hw
  obtain ⟨χw, hχwsmooth, hχwfeat, -⟩ := hcorrect w hw
  let Y : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N w (HRS.Whole.pair ν w) X
  let rp : EucConfig p.d N → ℝ := fun X =>
    s45_Rp (HRS.Whole.withDensityReal (R.ρ 0))
      (S47.s47_nu p.d p.s (R.ρ 0) p.γ N)
      (S47.s47_P p.d p.s (R.ρ 0) p.γ N)
      (commutatorKernel p.d p.s (gradient χw)) X
  let Rlin : ℝ := ∫ X, (Real.sqrt N * rp X) * ψ (W X) ∂P
  let w2 : ℕ → Euc p.d → ℝ := fun m x =>
    p.γ⁻¹ * ⟪gradient χw x, gradient (φ m) x⟫
  let Cm : ℕ → ℝ := fun m => p.γ⁻¹ * (K₂ * cw) * b m
  have hCm0 : ∀ m, 0 ≤ Cm m := fun m => by
    have := hb0 m
    positivity
  have hDφ : ∀ m x, ‖fderiv ℝ (φ m) x‖ ≤ b m := fun m x =>
    s45_cb_deriv_le hJ (hφ.1 m) x
  have hBφ : ∀ m x, |φ m x| ≤ b m := fun m x => by
    have hh := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 m) x
    rwa [Real.norm_eq_abs] at hh
  have hφm1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m =>
    (hφ.1 m).1.of_le (by exact_mod_cast hJ)
  have hw2bd : ∀ m x, |w2 m x| ≤ Cm m := by
    intro m x
    simp only [w2, Cm]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left
      (S99.s99_inner_grad_le hχwfeat.B1 (hDφ m) x) (inv_nonneg.2 hγ.le)).trans_eq (by ring)
  have hw2c : ∀ m, Continuous (w2 m) := fun m =>
    continuous_const.mul ((s45_contDiff_gradient hχwsmooth).continuous.inner
      (s45_gradient_continuous (hφm1 m)))
  have hcc : ∀ m, fp81s21_initial_kap (R := R) w φ m =
      ∫ x, w2 m x ∂(r26t3_mu R 0) := by
    intro m
    have hφm : MemLp (φ m) 2 (r26t3_mu R 0) := HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 m)
    have hcovResp := fp81s21_initial_cov_response_integral E hγ hφ F hw m
    have hcovSym := fp81s21_initial_covariance_symmetric E hγ hwl2 hφm
    have hcovW := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
      hχwfeat.smooth hχwfeat.B1 hχwfeat.B2 hwl2 hχwfeat.r2 hχwfeat.corr
      (hφm1 m) (Bφ := b m) (Dφ := b m) (hBφ m) (hDφ m)
    calc
      fp81s21_initial_kap (R := R) w φ m =
          ∫ x, w x * r26t3_a R (φ m) x ∂(r26t3_mu R 0) := rfl
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (φ m) w := hcovResp.symm
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ w (φ m) := hcovSym.symm
      _ = p.γ⁻¹ * ∫ x, ⟪gradient χw x, gradient (φ m) x⟫
          ∂(HRS.Whole.withDensityReal (R.ρ 0)) := hcovW
      _ = ∫ x, w2 m x ∂(r26t3_mu R 0) := by
        have hμeq : r26t3_mu R 0 = HRS.Whole.withDensityReal (R.ρ 0) := rfl
        rw [hμeq]
        simp only [w2]
        rw [integral_const_mul]
  have hcmBd : ∀ m, |∫ x, w2 m x ∂(r26t3_mu R 0)| ≤ Cm m := by
    intro m
    have hh := norm_integral_le_of_norm_le_const
      (μ := r26t3_mu R 0) (f := w2 m) (C := Cm m)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hw2bd m x)
    simpa [Real.norm_eq_abs] using hh
  let hT2 : ℕ → EucConfig p.d N → ℝ := fun m X =>
    p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χw x, gradient (φ m) x⟫)
  have hT2e : ∀ m X, hT2 m X = HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) := by
    intro m X
    change p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χw x, gradient (φ m) x⟫) =
      HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => p.γ⁻¹ * ⟪gradient χw x, gradient (φ m) x⟫)
    exact (S99.s99_pair_smul hN1 p.γ⁻¹ _ X).symm
  have hT2m : ∀ m, Measurable (hT2 m) := fun m => by
    have he : hT2 m = fun X => HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) :=
      funext (hT2e m)
    rw [he]
    exact s45_measurable_pair_empirical hN1 (hw2c m).measurable
  have hT2bd : ∀ m X, |hT2 m X| ≤ Cm m := fun m X => by
    rw [hT2e]
    exact s45_abs_pair_empirical_le hN1 (hw2bd m) X
  have hpdm : ∀ m, S99.Bd 2 (S99.pd ψ m) := fun m => hψ.pd m
  have hpdmM : ∀ m, Measurable fun X : EucConfig p.d N =>
      S99.pd ψ m (W X) := fun m => ((hpdm m).1.continuous.comp hWc).measurable
  have hTmInt : ∀ m, Integrable
      (fun X : EucConfig p.d N => hT2 m X * S99.pd ψ m (W X)) P := by
    intro m
    refine Integrable.of_bound ((hT2m m).mul (hpdmM m)).aestronglyMeasurable
      (Cm m) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |hT2 m X| * |S99.pd ψ m (W X)| ≤ Cm m * 1 :=
          mul_le_mul (hT2bd m X) ((hpdm m).abs_le _) (abs_nonneg _) (hCm0 m)
      _ = Cm m := mul_one _
  have hRpIntSrc := S47.s47_Rp_integrable p.hd p.hs0 hsd E.reference hN
    (E.static N hN) hχwsmooth hχwfeat.B2
  have hRpInt : Integrable rp P := by
    change Integrable
      (s45_Rp (HRS.Whole.withDensityReal (R.ρ 0))
        (S47.s47_nu p.d p.s (R.ρ 0) p.γ N)
        (S47.s47_P p.d p.s (R.ρ 0) p.γ N)
        (commutatorKernel p.d p.s (gradient χw))) (r26t3_Q R N)
    rw [← E.law_eq N]
    exact hRpIntSrc
  have hRint : Integrable (fun X : EucConfig p.d N =>
      (Real.sqrt N * rp X) * ψ (W X)) P := by
    have hh : Integrable (fun X : EucConfig p.d N =>
        ψ (W X) * (Real.sqrt N * rp X)) P := by
      refine (hRpInt.const_mul (Real.sqrt N)).bdd_mul (c := 1)
        hψWm.aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]
      exact hψWbd X
    exact hh.congr (Filter.Eventually.of_forall fun X => by ring)
  have hsourceP : S47.s47_P p.d p.s (R.ρ 0) p.γ N = P := E.law_eq N
  have hsourceNu : S47.s47_nu p.d p.s (R.ρ 0) p.γ N = ν := by
    change HRS.Whole.firstMarginal (S47.s47_P p.d p.s (R.ρ 0) p.γ N) =
      HRS.Whole.firstMarginal (r26t3_Q R N)
    rw [hsourceP]
  have hRpEq : ∀ X, rp X = -(HRS.Whole.pairEnergy
      (commutatorKernel p.d p.s (gradient χw)) X (r26t3_mu R 0) -
        ∫ Z, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) Z
          (r26t3_mu R 0) ∂P) := by
    intro X
    have hh := fp81s21_s47_Rp_eq p.hd p.hs0 hsd E.reference hN
      (E.static N hN) hχwsmooth hχwfeat.B2 X
    simpa [rp, P, ν, r26t3_mu, hsourceP, hsourceNu] using hh
  have hRboundAct : Real.sqrt N * ∫ X, |rp X| ∂P ≤
      KR * (K₂ * cw) * Real.sqrt (HRS.deltaN p.d p.s N) := by
    have hh := hRbound E.reference E.static N hN hχwsmooth
      (B2 := K₂ * cw) hχwfeat.B2
    rw [← hsourceP]
    exact hh
  have hR : |Rlin| ≤ KR * (K₂ * cw) / Real.sqrt N := by
    have hdom : Integrable (fun X : EucConfig p.d N => Real.sqrt N * |rp X|) P :=
      hRpInt.abs.const_mul (Real.sqrt N)
    have hpt : ∀ X : EucConfig p.d N,
        ‖(Real.sqrt N * rp X) * ψ (W X)‖ ≤ Real.sqrt N * |rp X| := by
      intro X
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      calc
        Real.sqrt N * |rp X| * |ψ (W X)| ≤ Real.sqrt N * |rp X| * 1 :=
          mul_le_mul_of_nonneg_left (hψWbd X)
            (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        _ = Real.sqrt N * |rp X| := mul_one _
    have h1 : |Rlin| ≤ ∫ X, ‖(Real.sqrt N * rp X) * ψ (W X)‖ ∂P := by
      dsimp [Rlin]
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ X, ‖(Real.sqrt N * rp X) * ψ (W X)‖ ∂P ≤
        ∫ X, Real.sqrt N * |rp X| ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _)
        hdom (Filter.Eventually.of_forall hpt)
    calc
      |Rlin| ≤ ∫ X, ‖(Real.sqrt N * rp X) * ψ (W X)‖ ∂P := h1
      _ ≤ ∫ X, Real.sqrt N * |rp X| ∂P := h2
      _ = Real.sqrt N * ∫ X, |rp X| ∂P := integral_const_mul _ _
      _ ≤ KR * (K₂ * cw) * Real.sqrt (HRS.deltaN p.d p.s N) := hRboundAct
      _ = KR * (K₂ * cw) / Real.sqrt N := by rw [hsqrtδ]; ring
  have hE := fp81s21_initial_plain_response E hγ hN hφ hw hχwfeat
    (ψ := ψ) (hψ.of_le (by omega))
  have hfirst : -(Real.sqrt N) * ∫ X,
      (HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) X (r26t3_mu R 0) -
        ∫ Z, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) Z
          (r26t3_mu R 0) ∂P) * ψ (W X) ∂P = Rlin := by
    dsimp [Rlin]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    change -(Real.sqrt N) *
        ((HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) X
            (r26t3_mu R 0) -
          ∫ Z, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) Z
            (r26t3_mu R 0) ∂P) * ψ (W X)) =
      (Real.sqrt N * rp X) * ψ (W X)
    rw [hRpEq X]
    ring
  have hE' : ∫ X, Y X * ψ (W X) ∂P = Rlin + ∑' m,
      ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P := by
    calc
      _ = -(Real.sqrt N) * ∫ X,
          (HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) X (r26t3_mu R 0) -
            ∫ Z, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χw)) Z
              (r26t3_mu R 0) ∂P) * ψ (W X) ∂P +
          ∑' m, ∫ X, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χw x, gradient (φ m) x⟫)) *
            S99.pd ψ m (W X) ∂P := hE
      _ = Rlin + ∑' m, ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P := by
          rw [hfirst]
  have hdiff : ∀ m, |(∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) -
      fp81s21_initial_kap (R := R) w φ m * ∫ z, S99.pd ψ m z ∂G| ≤
        (KT + Kclt) * Cm m / Real.sqrt N := by
    intro m
    obtain ⟨hiQ, hiG, hCLT⟩ := hclt N hN (hpdm m)
    set cmv : ℝ := ∫ x, w2 m x ∂(r26t3_mu R 0)
    rw [hcc m]
    have hdecomp :
        (∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) - cmv * ∫ z, S99.pd ψ m z ∂G =
          (∫ X, (hT2 m X - cmv) * S99.pd ψ m (W X) ∂P) +
            cmv * ((∫ X, S99.pd ψ m (W X) ∂P) - ∫ z, S99.pd ψ m z ∂G) := by
      have hInt : ∫ X, (hT2 m X - cmv) * S99.pd ψ m (W X) ∂P =
          (∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) -
            cmv * ∫ X, S99.pd ψ m (W X) ∂P := by
        rw [← integral_const_mul, ← integral_sub (hTmInt m) (hiQ.const_mul cmv)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only
        ring
      rw [hInt]
      ring
    rw [hdecomp]
    have hL1src := hTbound E.reference E.static N hN
      (hw2c m).measurable (Bf := Cm m) (hw2bd m)
    have hL1 : ∫ X, |HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) -
        HRS.Whole.pair (r26t3_mu R 0) (w2 m)| ∂P ≤
          KT * Cm m / Real.sqrt N := by
      have hh := hL1src
      rw [← hsourceP]
      calc
        _ ≤ KT * Cm m * Real.sqrt (HRS.deltaN p.d p.s N) := hh
        _ = KT * Cm m / Real.sqrt N := by rw [hsqrtδ]; ring
    have e1 : |∫ X, (hT2 m X - cmv) * S99.pd ψ m (W X) ∂P| ≤
        KT * Cm m / Real.sqrt N := by
      have hpt : ∀ X : EucConfig p.d N,
          ‖(hT2 m X - cmv) * S99.pd ψ m (W X)‖ ≤
            |HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) -
              HRS.Whole.pair (r26t3_mu R 0) (w2 m)| := by
        intro X
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hT2e]
        have hcmv : HRS.Whole.pair (r26t3_mu R 0) (w2 m) = cmv := rfl
        rw [hcmv]
        calc
          |HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) - cmv| *
              |S99.pd ψ m (W X)| ≤
            |HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) - cmv| * 1 :=
              mul_le_mul_of_nonneg_left ((hpdm m).abs_le _) (abs_nonneg _)
          _ = _ := mul_one _
      have hDiffInt : Integrable (fun X : EucConfig p.d N =>
          |HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) -
            HRS.Whole.pair (r26t3_mu R 0) (w2 m)|) P := by
        refine Integrable.of_bound (((s45_measurable_pair_empirical hN1
          (hw2c m).measurable).sub measurable_const).abs).aestronglyMeasurable
          (Cm m + Cm m) (Filter.Eventually.of_forall fun X => ?_)
        rw [Real.norm_eq_abs, abs_abs]
        have h1 := s45_abs_pair_empirical_le hN1 (hw2bd m) X
        have h2 : |HRS.Whole.pair (r26t3_mu R 0) (w2 m)| ≤ Cm m :=
          HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hw2bd m x)
        exact (abs_sub _ _).trans (add_le_add h1 h2)
      have h1 := norm_integral_le_integral_norm (μ := P)
        (fun X : EucConfig p.d N => (hT2 m X - cmv) * S99.pd ψ m (W X))
      have h2 := integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun X => norm_nonneg _)
        hDiffInt (Filter.Eventually.of_forall hpt)
      rw [← Real.norm_eq_abs]
      exact h1.trans (h2.trans hL1)
    have e2 : |cmv * ((∫ X, S99.pd ψ m (W X) ∂P) -
        ∫ z, S99.pd ψ m z ∂G)| ≤ Kclt * Cm m / Real.sqrt N := by
      rw [abs_mul]
      calc
        |cmv| * |(∫ X, S99.pd ψ m (W X) ∂P) -
            ∫ z, S99.pd ψ m z ∂G| ≤ Cm m * (Kclt / Real.sqrt N) :=
          mul_le_mul (hcmBd m) hCLT (abs_nonneg _) (hCm0 m)
        _ = Kclt * Cm m / Real.sqrt N := by ring
    calc
      _ ≤ |∫ X, (hT2 m X - cmv) * S99.pd ψ m (W X) ∂P| +
          |cmv * ((∫ X, S99.pd ψ m (W X) ∂P) -
            ∫ z, S99.pd ψ m z ∂G)| := abs_add_le _ _
      _ ≤ KT * Cm m / Real.sqrt N + Kclt * Cm m / Real.sqrt N := add_le_add e1 e2
      _ = (KT + Kclt) * Cm m / Real.sqrt N := by ring
  let Tm : ℕ → ℝ := fun m => ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P
  let Gm : ℕ → ℝ := fun m => ∫ z, S99.pd ψ m z ∂G
  have hCmS : Summable Cm := hbs.mul_left (p.γ⁻¹ * (K₂ * cw))
  have hTmBd : ∀ m, ‖Tm m‖ ≤ Cm m := by
    intro m
    have hh := norm_integral_le_of_norm_le_const
      (μ := P) (f := fun X => hT2 m X * S99.pd ψ m (W X)) (C := Cm m)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |hT2 m X| * |S99.pd ψ m (W X)| ≤ Cm m * 1 :=
            mul_le_mul (hT2bd m X) ((hpdm m).abs_le _) (abs_nonneg _) (hCm0 m)
          _ = Cm m := mul_one _)
    simpa [Tm] using hh
  have hGmBd : ∀ m, |Gm m| ≤ 1 := by
    intro m
    have hh := norm_integral_le_of_norm_le_const
      (μ := G) (f := fun z => S99.pd ψ m z) (C := 1)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hpdm m).abs_le z)
    simpa [Gm, Real.norm_eq_abs] using hh
  have hκGmBd : ∀ m, ‖fp81s21_initial_kap (R := R) w φ m * Gm m‖ ≤ Cm m := by
    intro m
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hcc m]
    calc
      |∫ x, w2 m x ∂(r26t3_mu R 0)| * |Gm m| ≤ Cm m * 1 :=
        mul_le_mul (hcmBd m) (hGmBd m) (abs_nonneg _) (hCm0 m)
      _ = Cm m := mul_one _
  have hsumT : Summable Tm := Summable.of_norm_bounded hCmS hTmBd
  have hsumG : Summable fun m => fp81s21_initial_kap (R := R) w φ m * Gm m :=
    Summable.of_norm_bounded hCmS hκGmBd
  have hdecomp :
      (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m * Gm m =
        Rlin + ∑' m, (Tm m - fp81s21_initial_kap (R := R) w φ m * Gm m) := by
    rw [hE', show (∑' m, ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) = ∑' m, Tm m by rfl,
      hsumT.tsum_sub hsumG]
    ring
  have hser : |∑' m, (Tm m - fp81s21_initial_kap (R := R) w φ m * Gm m)| ≤
      (KT + Kclt) / Real.sqrt N * (p.γ⁻¹ * (K₂ * cw) * Sb) := by
    have hg : HasSum (fun m => (KT + Kclt) / Real.sqrt N * Cm m)
        ((KT + Kclt) / Real.sqrt N * ∑' m, Cm m) := hCmS.hasSum.mul_left _
    have hCsum : ∑' m, Cm m = p.γ⁻¹ * (K₂ * cw) * Sb := by
      simp only [Cm]
      rw [tsum_mul_left]
    rw [hCsum] at hg
    have hh := tsum_of_norm_bounded hg
      (f := fun m => Tm m - fp81s21_initial_kap (R := R) w φ m * Gm m)
      (fun m => by
        rw [Real.norm_eq_abs]
        refine (hdiff m).trans (le_of_eq ?_)
        ring)
    simpa [Real.norm_eq_abs] using hh
  have hYeq :
      (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m * Gm m =
        (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m * ∫ z, S99.pd ψ m z ∂G := by
    apply congrArg (fun z : ℝ =>
      (∫ X, Y X * ψ (W X) ∂P) - z)
    apply tsum_congr
    intro m
    simp [Gm]
  have hfinish :
      |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m * ∫ z, S99.pd ψ m z ∂G| ≤
        KL * cw / Real.sqrt N := by
    rw [← hYeq, hdecomp]
    calc
      |Rlin + ∑' m, (Tm m - fp81s21_initial_kap w φ m * Gm m)| ≤
          |Rlin| + |∑' m, (Tm m - fp81s21_initial_kap (R := R) w φ m * Gm m)| := abs_add_le _ _
      _ ≤ KR * (K₂ * cw) / Real.sqrt N +
          (KT + Kclt) / Real.sqrt N * (p.γ⁻¹ * (K₂ * cw) * Sb) := add_le_add hR hser
      _ = KL * cw / Real.sqrt N := by simp [KL]; ring
  simpa [Y, W, P, ν, cw] using hfinish

/-- The finite-`N` linear coefficient at the actual initial law, with the same normalization
as `S99.Aterm`. -/
def fp81s21_initial_Aterm {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (N : ℕ)
    (f : SeqL2 → ℝ) (q : ℕ × ℕ) : ℝ :=
  Real.sqrt N * ∫ X,
    (fp81s21_initial_Cf F q.1 q.2 -
      HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F q.1 q.2)) *
      S99.pd (S99.pd f q.1) q.2 (featureVec φ (r26t3_marg R N) X)
    ∂(r26t3_Q R N)

/-- The feature-series limit of `fp81s21_initial_Aterm`, with the nonthermal response coefficient.
-/
def fp81s21_initial_Alim {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (G : Measure SeqL2)
    (f : SeqL2 → ℝ) (q : ℕ × ℕ) : ℝ :=
  -∑' m, fp81s21_initial_kap (R := R) (InitialFamData.wF F q.1 q.2) φ m *
    ∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G

/-- The S9.9 coefficient rate at the actual initial law. The constant is fixed before `N`, the
Stein test, and the coefficient indices. -/
theorem fp81s21_initial_A_rate
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (φ i) (φ j))) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ,
      S99.SteinCl f → ∀ q : ℕ × ℕ,
      |fp81s21_initial_Aterm F N f q - fp81s21_initial_Alim F G f q| ≤
        KA * (cbNorm (fp81s21_J1 p.d) (φ q.1) *
          cbNorm (fp81s21_J1 p.d) (φ q.2)) / Real.sqrt N := by
  obtain ⟨KL, hKL, hYlin⟩ :=
    fp81s21_initial_Ylin hδ hδh R E hγ hφ F hG
  let J : ℕ := fp81s21_k0 p.d
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hJ : 1 ≤ J := by dsimp [J]; exact fp81s21_k0_ge_one p.d
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hFK : 0 ≤ F.K := F.hK
  have hCs : 0 ≤ E.Cs := E.Cs_nonneg
  let Kw : ℝ := ((J : ℝ) + 1) * 2 ^ J * (p.γ⁻¹ * F.K)
  let KA : ℝ := Kw * (KL + E.Cs * ((J : ℝ) + 1))
  have hKw0 : 0 ≤ Kw := by
    dsimp [Kw]
    positivity
  have hKA0 : 0 ≤ KA := by
    dsimp [KA]
    positivity
  refine ⟨KA, hKA0, fun N hN f hf q => ?_⟩
  obtain ⟨j, k⟩ := q
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  let w : Euc p.d → ℝ := InitialFamData.wF F j k
  let ψ : SeqL2 → ℝ := S99.pd (S99.pd f j) k
  let Y : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N w (HRS.Whole.pair ν w) X
  let β0 : ℝ := Real.sqrt N *
    (HRS.Whole.pair ν w - fp81s21_initial_Cf F j k)
  have hψ : S99.Bd 3 ψ := (hf.pd j).pd k
  have hJ1 : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hWc : Continuous W := (S99.s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψWbd : ∀ X, |ψ (W X)| ≤ 1 := fun X => hψ.abs_le _
  have hψWm : Measurable fun X : EucConfig p.d N => ψ (W X) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψWint : Integrable (fun X : EucConfig p.d N => ψ (W X)) P :=
    Integrable.of_bound hψWm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hψWbd X)
  have hwcb := fp81s21_initial_wF_cb hφ.1 F hγ j k
  have hwbd : ∀ x, |w x| ≤ cbNorm J w := by
    intro x
    have hh := HRS.MS.Tc5.tc5_cb_sup_le hwcb.1 x
    rwa [Real.norm_eq_abs] at hh
  have hwm : Measurable w := hwcb.1.1.continuous.measurable
  have hcw : cbNorm J w ≤ Kw * (b j * b k) := by
    calc
      cbNorm J w ≤ ((J : ℝ) + 1) * 2 ^ J *
          (p.γ⁻¹ * F.K * b j) * b k := by
        simpa [J, b, w] using hwcb.2
      _ = Kw * (b j * b k) := by dsimp [Kw]; ring
  have hcw0 : 0 ≤ cbNorm J w := HRS.MS.Tc5.tc5_cb_nonneg J w
  have hYbd : ∀ X, |Y X| ≤ 2 * Real.sqrt N * cbNorm J w := by
    intro X
    simp only [Y, s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 hwbd X
    have h2 : |HRS.Whole.pair ν w| ≤ cbNorm J w :=
      HRS.MS.Tc5.tc5_pair_le (fun x => by
        rw [Real.norm_eq_abs]
        exact hwbd x)
    calc
      Real.sqrt N * |HRS.Whole.pair (HRS.Whole.empirical X) w -
          HRS.Whole.pair ν w| ≤
        Real.sqrt N * (|HRS.Whole.pair (HRS.Whole.empirical X) w| +
          |HRS.Whole.pair ν w|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (cbNorm J w + cbNorm J w) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * cbNorm J w := by ring
  have hYm : Measurable Y :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hwm).sub measurable_const)
  have hYψint : Integrable (fun X : EucConfig p.d N => Y X * ψ (W X)) P :=
    Integrable.of_bound (hYm.mul hψWm).aestronglyMeasurable
      (2 * Real.sqrt N * cbNorm J w)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |Y X| * |ψ (W X)| ≤ (2 * Real.sqrt N * cbNorm J w) * 1 :=
            mul_le_mul (hYbd X) (hψWbd X) (abs_nonneg _)
              (by positivity)
          _ = 2 * Real.sqrt N * cbNorm J w := mul_one _)
  have hCf : fp81s21_initial_Cf F j k =
      HRS.Whole.pair (r26t3_mu R 0) w := by
    calc
      fp81s21_initial_Cf F j k =
          ∫ x, w x ∂(r26t3_mu R 0) := by
        simpa [w] using fp81s21_initial_Cf_eq_wF E hγ hφ F j k
      _ = HRS.Whole.pair (r26t3_mu R 0) w := rfl
  have hA1 : fp81s21_initial_Aterm F N f (j, k) =
      -(∫ X, Y X * ψ (W X) ∂P) - β0 * ∫ X, ψ (W X) ∂P := by
    unfold fp81s21_initial_Aterm
    simp only
    rw [← integral_const_mul, ← integral_const_mul, ← integral_neg, ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [Y, β0, s45_Yi, hCf]
      ring
    · exact hYψint.neg
    · exact hψWint.const_mul _
  have hEx : HRS.Whole.IsExchangeable P := by
    dsimp [P]
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hEmp : ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) w ∂P =
      HRS.Whole.pair ν w :=
    s45_E_pair_empirical hN1 hEx hwm hwbd
  have hcfBias := fp81s21_initial_Cf_bias_s48 E hγ hφ F N hN j k
  have hcfBias' :
      |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := by
    dsimp [P, ν, w] at hEmp ⊢
    rw [← hEmp]
    exact hcfBias
  have hmargBias := fp81s21_initial_marginal_bias_s48 E hN (J := J) hwcb.1
  have hmargBias' :
      |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := by
    rw [hCf]
    simpa [ν, w] using hmargBias
  have hQcb : HRS.MS.S48.s48_Q (r26t3_mu R 0) J w ≤
      ((J : ℝ) + 1) * cbNorm J w := by
    simpa [J, w] using fp81s21_s48_Q_le_cb
      (μ := r26t3_mu R 0) (w := w) hwcb.1
  have hDiff : |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
      E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ) := by
    have hboth :
        max |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k|
            |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
          E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) :=
      max_le hmargBias' hcfBias'
    have hbase : |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) :=
      (le_max_left _ _).trans hboth
    calc
      _ ≤ E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := hbase
      _ ≤ E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w ≤
              E.Cs * (((J : ℝ) + 1) * cbNorm J w) :=
            mul_le_mul_of_nonneg_left hQcb hCs
          _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w := by ring
  have hβ0 : |β0| ≤ E.Cs * ((J : ℝ) + 1) * Kw *
      (b j * b k) / Real.sqrt N := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt hN0.le
    dsimp [β0]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
          Real.sqrt N * (E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hDiff (Real.sqrt_nonneg _)
      _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w / Real.sqrt N := by
        rw [eq_div_iff hsqN.ne']
        calc
          Real.sqrt N * (E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ)) *
              Real.sqrt N =
            (Real.sqrt N * Real.sqrt N) *
              (E.Cs * ((J : ℝ) + 1) * cbNorm J w) / (N : ℝ) := by ring
          _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w := by rw [hsq]; field_simp
      _ ≤ E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) / Real.sqrt N := by
        apply div_le_div_of_nonneg_right _ hsqN.le
        calc
          E.Cs * ((J : ℝ) + 1) * cbNorm J w ≤
              E.Cs * ((J : ℝ) + 1) * (Kw * (b j * b k)) :=
            mul_le_mul_of_nonneg_left hcw (by positivity)
          _ = E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) := by ring
  have hψint : |∫ X, ψ (W X) ∂P| ≤ 1 := by
    have hh := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => ψ (W X)) (C := 1)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hψWbd X)
    simpa [Real.norm_eq_abs] using hh
  have hYerr :
      |(∫ X, Y X * ψ (W X) ∂P) -
        ∑' m, fp81s21_initial_kap (R := R) w φ m *
          ∫ z, S99.pd ψ m z ∂G| ≤ KL * Kw * (b j * b k) / Real.sqrt N := by
    have hh := hYlin N hN (w := w) hwcb.1 (ψ := ψ) hψ
    have hh' :
        |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G| ≤ KL * cbNorm J w / Real.sqrt N := by
      simpa [Y, P, ν, W, w] using hh
    calc
      _ ≤ KL * cbNorm J w / Real.sqrt N := hh'
      _ ≤ KL * Kw * (b j * b k) / Real.sqrt N := by
        apply div_le_div_of_nonneg_right _ hsqN.le
        calc
          KL * cbNorm J w ≤ KL * (Kw * (b j * b k)) :=
            mul_le_mul_of_nonneg_left hcw hKL
          _ = KL * Kw * (b j * b k) := by ring
  have hdecomp :
      fp81s21_initial_Aterm F N f (j, k) -
          fp81s21_initial_Alim F G f (j, k) =
        -((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P := by
    rw [hA1]
    simp only [fp81s21_initial_Alim, ψ]
    ring
  have htriangle :
      |-((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P| ≤
        |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G| + |β0| := by
    calc
      _ ≤ |(∫ X, Y X * ψ (W X) ∂P) -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G| +
          |β0 * ∫ X, ψ (W X) ∂P| := by
        simpa only [abs_neg] using abs_sub
          (-(∫ X, Y X * ψ (W X) ∂P -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G))
          (β0 * ∫ X, ψ (W X) ∂P)
      _ ≤ |(∫ X, Y X * ψ (W X) ∂P) -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G| + |β0| * 1 :=
        add_le_add le_rfl (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hψint (abs_nonneg β0))
      _ = _ := by rw [abs_mul]; ring
  calc
    |fp81s21_initial_Aterm F N f (j, k) - fp81s21_initial_Alim F G f (j, k)| =
        |-((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P| := by rw [hdecomp]
    _ ≤ KL * Kw * (b j * b k) / Real.sqrt N +
        E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) / Real.sqrt N := by
      exact htriangle.trans (add_le_add hYerr hβ0)
    _ = KA * (cbNorm (fp81s21_J1 p.d) (φ j) *
        cbNorm (fp81s21_J1 p.d) (φ k)) / Real.sqrt N := by
      simp only [KA, b]
      ring

#print axioms fp81s21_initial_cov_response_integral
#print axioms fp81s21_s48_Q_le_cb
#print axioms fp81s21_initial_covariance_symmetric
#print axioms fp81s21_initial_Ylin
#print axioms fp81s21_initial_A_rate

end HRS.Fp81.S21

end
