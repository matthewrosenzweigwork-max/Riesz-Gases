import HRS.MS.Fp81S21InitialLinear3
import HRS.MS.R2SeAux22

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

/-!
## SOL31 packet 24b: thermal source contract and actual-law dictionary

The exact thermal statement in `R2SeAux25:35` is

```
S99.s99_Mab
  (hG : IsCenteredGaussianSeq G
    (fun i j => susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β)
      γ (φ i) (φ j)))
  (hu : MemCb (J1 d) u) (hv : MemCb (J1 d) v) :
  ∃ K, 0 ≤ K ∧ ∀ N, 2 ≤ N → ∀ {ψ}, Bd 4 ψ →
    |(∫ Y_u * (Y_v * ψ(W)) ∂(S46.s46_P ... N))
      - (∫ Y_u * Y_v ∂(S46.s46_P ... N)) * (∫ ψ(W) ∂(S46.s46_P ... N))
      - ∑' l, ∑' q, kap ... u ... l * kap ... v ... q
          * ∫ pd (pd ψ l) q dG| ≤ K / sqrt N.
```

Its compiled proof closure is `s99_chi1`, `s99_Bq_bound`, `s99_T_L2`,
`s99_Y_L2`, `s99_Mab_l`, `s99_E1b` (for `ψ` and `1`), `s99_T_L1`,
and generic bounded-test algebra. The initial-law ports already available are
`fp81s21_initial_orderOne_corrector`, `fp81s21_initial_Bq_bound`,
`fp81s21_initial_T_L2`, `fp81s21_initial_T_L1`, `fp81s21_initial_Y_L2`,
`fp81s21_initial_clt`, `fp81s21_initial_Ylin`, `fp81s21_initial_A_rate`,
and `fp81s21_initial_kap`. The mixed response and per-index quadratic limit
are the remaining analytic interfaces at this stage.

The actual-law dictionary follows the compiled definitions: `r26t3_mu R 0`
is `withDensityReal (R.ρ 0)`, `r26t3_Q R N` is the modulated Gibbs law at
that measure, and `r26t3_marg R N` is its first marginal. `InitialSteinEnv`
identifies `r26t3_Q R N` with the S47 static law and supplies its probability,
exchangeability, and static certificates. The Gaussian covariance uses
`r26t3_mu R 0`, and the response coefficient is the exported
`fp81s21_initial_kap`; the thermal `thermalMeasure` and `kap` are not
substituted for these actual-law objects.

The following mixed response is proved directly from the compiled actual-law
`initial_stein_pairEnergy` and generic `S99.s99_fderivF_apply`. Thus its
replacement for thermal `s99_E1b` uses the S47 exact response at `R.ρ 0`;
it invokes no thermal Euler equation at the preparation law.
-/

/-- The mixed S9.9 exact response identity at the actual preparation law. This is the
nonthermal analogue of `S99.s99_E1b`, with the S47 response and the actual initial marginal. -/
theorem fp81s21_initial_E1b
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {b u χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hb : MemCb (fp81s21_J1 p.d) b) (hu : MemCb (fp81s21_k0 p.d) u)
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ u χ Bχ)
    {ψ : SeqL2 → ℝ} (hψ : Bd 1 ψ) :
    ∫ X, s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X *
        (s45_Yi N b (HRS.Whole.pair (r26t3_marg R N) b) X *
          ψ (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N) =
      -(Real.sqrt N) * ∫ X,
          (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
            ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y
              (r26t3_mu R 0) ∂(r26t3_Q R N)) *
          (s45_Yi N b (HRS.Whole.pair (r26t3_marg R N) b) X *
            ψ (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N) +
        ∑' l, ∫ X,
          (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          (s45_Yi N b (HRS.Whole.pair (r26t3_marg R N) b) X *
            pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N) +
        ∫ X,
          (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient b x⟫)) *
          ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  let ν : Measure (Euc p.d) := r26t3_marg R N
  letI : IsProbabilityMeasure ν := hν
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  let Yb : EucConfig p.d N → ℝ := fun X => s45_Yi N b (HRS.Whole.pair ν b) X
  let T : EucConfig p.d N → ℝ := fun X => Yb X * ψ (W X)
  let ztest : SeqL2 × ℝ → ℝ := fun z => z.2 * ψ z.1
  let B : ℝ := cbNorm (fp81s21_J1 p.d) b
  let bs : ℕ → ℝ := fun l => cbNorm (fp81s21_J1 p.d) (φ l)
  let Csum : ℝ := Real.sqrt N * ∑' l, bs l
  have hB : 0 ≤ B := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs0 : ∀ l, 0 ≤ bs l := fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable bs := hφ.2
  have hCsum : 0 ≤ Csum :=
    mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg hbs0)
  have hb1 : ContDiff ℝ 1 b := hb.1.of_le (by exact_mod_cast hJ)
  have hbu : ContDiff ℝ 1 u := hu.1.of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast hk)
  have hWcd : ContDiff ℝ 1 W := S99.s99_W_contDiff hN1 hJ hφ
  have hWc : Continuous W := hWcd.continuous
  have hYcd : ContDiff ℝ 1 Yb :=
    s45_Yi_contDiff hN1 hb1 (HRS.Whole.pair ν b)
  have hYc : Continuous Yb := hYcd.continuous
  have hYbound : ∀ X, |Yb X| ≤ 2 * Real.sqrt N * B := by
    intro X
    dsimp [Yb, s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 (fun x => by
      have h := HRS.MS.Tc5.tc5_cb_sup_le hb x
      simpa [B, Real.norm_eq_abs] using h) X
    have h2 : |HRS.Whole.pair ν b| ≤ B :=
      HRS.MS.Tc5.tc5_pair_le (fun x => by
        have h := HRS.MS.Tc5.tc5_cb_sup_le hb x
        simpa [B, Real.norm_eq_abs] using h)
    calc Real.sqrt N * |HRS.Whole.pair (HRS.Whole.empirical X) b -
          HRS.Whole.pair ν b|
        ≤ Real.sqrt N * (|HRS.Whole.pair (HRS.Whole.empirical X) b| +
            |HRS.Whole.pair ν b|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (B + B) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * B := by ring
  have hψWbound : ∀ X, |ψ (W X)| ≤ 1 := fun X => hψ.abs_le _
  have hzcd : ContDiff ℝ 1 ztest :=
    contDiff_snd.mul (hψ.1.comp contDiff_fst)
  have hTcd : ContDiff ℝ 1 T := hYcd.mul (hψ.1.comp hWcd)
  have hTbound : ∀ X, |T X| ≤ (2 * Real.sqrt N * B) := by
    intro X
    dsimp [T]
    rw [abs_mul]
    calc |Yb X| * |ψ (W X)| ≤ (2 * Real.sqrt N * B) * 1 :=
          mul_le_mul (hYbound X) (hψWbound X) (abs_nonneg _) (by positivity)
      _ = 2 * Real.sqrt N * B := by ring
  have hWterm : ∀ X, ‖fderiv ℝ W X‖ ≤ Csum := by
    intro X
    have hWder := S99.s99_W_hasFDerivAt (ν := ν) hN1 hJ hφ X
    have hCLMnorm : Summable fun l : ℕ =>
        ‖(s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
        (hbs.mul_left (Real.sqrt N))
      exact S99.s99_Wterm_fderiv_norm hN1 hJ hφ.1 l X
    have hWfd : fderiv ℝ W X =
        ∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)) := hWder.fderiv
    rw [hWfd]
    calc ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖
        ≤ ∑' l, ‖(s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ :=
          norm_tsum_le_tsum_norm hCLMnorm
      _ ≤ ∑' l, Real.sqrt N * bs l :=
        Summable.tsum_le_tsum
          (fun l => S99.s99_Wterm_fderiv_norm hN1 hJ hφ.1 l X)
          hCLMnorm (hbs.mul_left (Real.sqrt N))
      _ = Csum := by dsimp [Csum]; rw [← tsum_mul_left]
  have hYterm : ∀ X, ‖fderiv ℝ Yb X‖ ≤ Real.sqrt N * B := by
    intro X
    have hYder := s45_Yi_hasFDerivAt hN1
      (hb1.differentiable (by norm_num)) (HRS.Whole.pair ν b) X
    have hYfd : fderiv ℝ Yb X = s45_L N b X := hYder.fderiv
    rw [hYfd]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    simpa only [Real.norm_eq_abs] using s45_L_bound (fun x => by
      have h := s45_cb_deriv_le hJ hb x
      simpa [B] using h) hN1 X z
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable one_ne_zero
  have hWder (X : EucConfig p.d N) :
      HasFDerivAt W
        (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) X := by
    simpa [W] using S99.s99_W_hasFDerivAt (ν := ν) hN1 hJ hφ X
  have hWsum (X : EucConfig p.d N) :
      ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ ≤ Csum := by
    rw [← (hWder X).fderiv]
    exact hWterm X
  have hψWhas (X : EucConfig p.d N) :
      HasFDerivAt (fun Z => ψ (W Z))
        ((fderiv ℝ ψ (W X)).comp
          (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)))) X := by
    exact (hψd (W X)).hasFDerivAt.comp X
      (hWder X)
  have hYhas (X : EucConfig p.d N) :
      HasFDerivAt Yb (s45_L N b X) X :=
    s45_Yi_hasFDerivAt hN1 (hb1.differentiable (by norm_num))
      (HRS.Whole.pair ν b) X
  have hTderiv : ∀ X, ‖fderiv ℝ T X‖ ≤
      (2 * Real.sqrt N * B) * Csum + Real.sqrt N * B := by
    intro X
    have hprod := (hYhas X).mul (hψWhas X)
    have hprod' : fderiv ℝ T X =
        ψ (W X) • (s45_L N b X) + Yb X •
          ((fderiv ℝ ψ (W X)).comp
            (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)))) := by
      change fderiv ℝ (Yb * (fun Z => ψ (W Z))) X = _
      rw [hprod.fderiv]
      abel
    rw [hprod']
    have hnormψ : ‖fderiv ℝ ψ (W X)‖ ≤ 1 := hψ.fderiv_le (W X)
    have hcomp : ‖(fderiv ℝ ψ (W X)).comp
        (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)))‖ ≤ Csum := by
      calc ‖(fderiv ℝ ψ (W X)).comp
            (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)))‖
          ≤ ‖fderiv ℝ ψ (W X)‖ *
            ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * Csum := mul_le_mul hnormψ (hWsum X) (norm_nonneg _) zero_le_one
        _ = Csum := one_mul _
    calc ‖ψ (W X) • s45_L N b X +
          Yb X • ((fderiv ℝ ψ (W X)).comp
            (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))))‖
        ≤ ‖ψ (W X) • s45_L N b X‖ +
          ‖Yb X • ((fderiv ℝ ψ (W X)).comp
            (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))))‖ :=
            ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ |ψ (W X)| * ‖s45_L N b X‖ +
          |Yb X| * ‖(fderiv ℝ ψ (W X)).comp
            (∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ)))‖ := by
            rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (Real.sqrt N * B) + (2 * Real.sqrt N * B) * Csum := by
            apply add_le_add
            · have hy : ‖s45_L N b X‖ ≤ Real.sqrt N * B := by
                rw [← (hYhas X).fderiv]
                exact hYterm X
              exact mul_le_mul (hψWbound X) hy (norm_nonneg _)
                (by positivity)
            · exact mul_le_mul (hYbound X) hcomp (norm_nonneg _)
                (by positivity)
      _ = (2 * Real.sqrt N * B) * Csum + Real.sqrt N * B := by ring
  have hχ1 : MemCb 1 u :=
    (HRS.MS.Tc5.tc5_cb_mono (m := 1) (J := fp81s21_k0 p.d)
      (by have hk := fp81s21_k0_ge_one p.d; omega) hu).1
  have hstein := initial_stein_pairEnergy E hγ hN hχ hχ1 hTcd
    (BF := 2 * Real.sqrt N * B) hTbound
    (DF := (2 * Real.sqrt N * B) * Csum + Real.sqrt N * B) hTderiv
  let g : ℕ → EucConfig p.d N → ℝ := fun l X =>
      (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
        (Yb X * pd ψ l (W X))
  let M : ℕ → ℝ := fun l =>
      ((p.γ⁻¹ * Bχ) * (2 * Real.sqrt N * B)) * bs l
  have hBχ : 0 ≤ Bχ := (norm_nonneg _).trans (hχ.B1 0)
  have hγinv : 0 ≤ p.γ⁻¹ := inv_nonneg.2 hγ.le
  have hM0 : ∀ l, 0 ≤ M l := by
    intro l
    dsimp [M]
    exact mul_nonneg (mul_nonneg (mul_nonneg hγinv hBχ)
      (by positivity)) (hbs0 l)
  have hpdBound : ∀ l X, |pd ψ l (W X)| ≤ 1 := by
    intro l X
    unfold pd
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ ψ (W X) (s45_e1 l (1 : ℝ))‖
        ≤ ‖fderiv ℝ ψ (W X)‖ * ‖s45_e1 l (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := by
        exact mul_le_mul (hψ.fderiv_le _) (s99_e1_norm l).le
          (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hgbound : ∀ l X, |g l X| ≤ M l := by
    intro l X
    have hgradφ : ∀ x, ‖gradient (φ l) x‖ ≤ bs l := by
      intro x
      rw [s45_norm_gradient]
      exact s45_cb_deriv_le hJ (hφ.1 l) x
    have hinner : ∀ x,
        |⟪gradient χ x, gradient (φ l) x⟫| ≤ Bχ * bs l := by
      intro x
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hχ.B1 x) (hgradφ x) (norm_nonneg _) hBχ)
    have hemp := s45_abs_pair_empirical_le hN1 hinner X
    have hcoeff : |p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| ≤
          p.γ⁻¹ * (Bχ * bs l) := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
      exact mul_le_mul_of_nonneg_left hemp (inv_nonneg.2 hγ.le)
    have hrest : |Yb X * pd ψ l (W X)| ≤ (2 * Real.sqrt N * B) * 1 := by
      rw [abs_mul]
      exact mul_le_mul (hYbound X) (hpdBound l X) (abs_nonneg _)
        (by positivity)
    calc |g l X| =
          |p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| *
            |Yb X * pd ψ l (W X)| := by simp [g, abs_mul]
      _ ≤ (p.γ⁻¹ * (Bχ * bs l)) * ((2 * Real.sqrt N * B) * 1) :=
          mul_le_mul hcoeff hrest (abs_nonneg _)
            (mul_nonneg hγinv (mul_nonneg hBχ (hbs0 l)))
      _ = M l := by dsimp [M]; ring
  have hgintegrable : ∀ l, AEStronglyMeasurable (g l) (r26t3_Q R N) := by
    intro l
    have hφ1 : ContDiff ℝ 1 (φ l) := (hφ.1 l).1.of_le (by exact_mod_cast hJ)
    have hinnerc : Continuous fun x : Euc p.d =>
        ⟪gradient χ x, gradient (φ l) x⟫ :=
      (s45_gradient_continuous (hχ.smooth.of_le (by norm_num))).inner
        (s45_gradient_continuous hφ1)
    have hpairm := s45_measurable_pair_empirical hN1 hinnerc.measurable
    have hpdcont : Continuous fun Z : SeqL2 => pd ψ l Z := by
      unfold pd
      exact (hψ.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hm : Measurable (g l) := by
      dsimp [g]
      have hcoeffm : Measurable (fun X : EucConfig p.d N => p.γ⁻¹ *
          HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) :=
        measurable_const.mul hpairm
      exact hcoeffm.mul (hYc.measurable.mul (hpdcont.comp hWc).measurable)
    exact hm.aestronglyMeasurable
  have hsumM : Summable M := by
    simpa [M] using hbs.mul_left ((p.γ⁻¹ * Bχ) * (2 * Real.sqrt N * B))
  have hseries := fp81s21_integral_tsum hsumM hgintegrable hgbound
  have hsumPoint : ∀ X : EucConfig p.d N,
      Summable (fun l => ‖g l X‖) := by
    intro X
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hsumM
    rw [Real.norm_eq_abs]
    exact hgbound l X
  have hsumBound : ∀ X : EucConfig p.d N,
      |∑' l, g l X| ≤ ∑' l, M l := by
    intro X
    rw [← Real.norm_eq_abs]
    calc ‖∑' l, g l X‖ ≤ ∑' l, ‖g l X‖ :=
          norm_tsum_le_tsum_norm (hsumPoint X)
      _ ≤ ∑' l, M l :=
          Summable.tsum_le_tsum (fun l => by
            rw [Real.norm_eq_abs]
            exact hgbound l X) (hsumPoint X) hsumM
  have hsumMeas : AEStronglyMeasurable
      (fun X : EucConfig p.d N => ∑' l, g l X) (r26t3_Q R N) :=
    (AEMeasurable.tsum fun l => (hgintegrable l).aemeasurable).aestronglyMeasurable
  have hsumInt : Integrable (fun X : EucConfig p.d N => ∑' l, g l X)
      (r26t3_Q R N) :=
    Integrable.of_bound hsumMeas (∑' l, M l)
      (Filter.Eventually.of_forall fun X => hsumBound X)
  have hinnerb : ∀ x,
      |⟪gradient χ x, gradient b x⟫| ≤ Bχ * B := by
    intro x
    have hbgrad : ‖gradient b x‖ ≤ B := by
      rw [s45_norm_gradient]
      exact s45_cb_deriv_le hJ hb x
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hχ.B1 x) hbgrad (norm_nonneg _) hBχ)
  have hpairbm := s45_measurable_pair_empirical hN1
    (show Measurable (fun x : Euc p.d => ⟪gradient χ x, gradient b x⟫) from
      ((s45_gradient_continuous (hχ.smooth.of_le (by norm_num))).inner
        (s45_gradient_continuous hb1)).measurable)
  have hψWm : Measurable (fun X : EucConfig p.d N => ψ (W X)) :=
    (hψ.1.continuous.comp hWc).measurable
  have hgbm : Measurable (fun X : EucConfig p.d N =>
      (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient b x⟫)) * ψ (W X)) := by
    have hc : Measurable (fun X : EucConfig p.d N => p.γ⁻¹ *
        HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient b x⟫)) := measurable_const.mul hpairbm
    exact hc.mul hψWm
  have hgboundB : ∀ X : EucConfig p.d N,
      |(p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient b x⟫)) * ψ (W X)| ≤
          p.γ⁻¹ * Bχ * B := by
    intro X
    have hemp := s45_abs_pair_empirical_le hN1 hinnerb X
    have hcoef : |p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient b x⟫)| ≤ p.γ⁻¹ * (Bχ * B) := by
      rw [abs_mul, abs_of_nonneg hγinv]
      exact mul_le_mul_of_nonneg_left hemp hγinv
    calc _ = |p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient b x⟫)| * |ψ (W X)| := by rw [abs_mul]
      _ ≤ (p.γ⁻¹ * (Bχ * B)) * 1 :=
          mul_le_mul hcoef (hψWbound X) (abs_nonneg _) (by positivity)
      _ = p.γ⁻¹ * Bχ * B := by ring
  have hgbInt : Integrable (fun X : EucConfig p.d N =>
      (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient b x⟫)) * ψ (W X))
      (r26t3_Q R N) :=
    Integrable.of_bound hgbm.aestronglyMeasurable (p.γ⁻¹ * Bχ * B)
      (Filter.Eventually.of_forall fun X => hgboundB X)
  have hdir : ∀ X,
      fderiv ℝ T X (fun i => gradient χ (X i)) =
        (p.γ * Real.sqrt N) *
          ((∑' l, g l X) +
            (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χ x, gradient b x⟫)) * ψ (W X)) := by
    intro X
    have hform := S99.s99_fderivF_apply (ν := ν) hN1 hJ hφ hb hzcd X
      (fun i => gradient χ (X i))
    have hZ : S99.Zq N φ b ν X = (W X, Yb X) := rfl
    rw [hZ] at hform
    have hcoord : ∀ l,
        fderiv ℝ ztest (W X, Yb X) (s45_e1 l (1 : ℝ), 0) =
          Yb X * pd ψ l (W X) := by
      intro l
      have hdψ := hψ.1.differentiable one_ne_zero
      have h1 : HasFDerivAt (fun z : SeqL2 × ℝ => z.2)
          (ContinuousLinearMap.snd ℝ SeqL2 ℝ) (W X, Yb X) := hasFDerivAt_snd
      have h2 : HasFDerivAt (fun z : SeqL2 × ℝ => ψ z.1)
          ((fderiv ℝ ψ (W X)).comp (ContinuousLinearMap.fst ℝ SeqL2 ℝ))
          (W X, Yb X) :=
        (hdψ (W X)).hasFDerivAt.comp (W X, Yb X)
          (hasFDerivAt_fst : HasFDerivAt (fun z : SeqL2 × ℝ => z.1)
            (ContinuousLinearMap.fst ℝ SeqL2 ℝ) (W X, Yb X))
      change fderiv ℝ ((fun z : SeqL2 × ℝ => z.2) *
        (fun z => ψ z.1)) (W X, Yb X) (s45_e1 l (1 : ℝ), 0) = _
      rw [(h1.mul h2).fderiv]
      simp [ztest, pd, smul_eq_mul]
    have hsecond :
        fderiv ℝ ztest (W X, Yb X) (0, 1) = ψ (W X) := by
      have hdψ := hψ.1.differentiable one_ne_zero
      have h1 : HasFDerivAt (fun z : SeqL2 × ℝ => z.2)
          (ContinuousLinearMap.snd ℝ SeqL2 ℝ) (W X, Yb X) := hasFDerivAt_snd
      have h2 : HasFDerivAt (fun z : SeqL2 × ℝ => ψ z.1)
          ((fderiv ℝ ψ (W X)).comp (ContinuousLinearMap.fst ℝ SeqL2 ℝ))
          (W X, Yb X) :=
        (hdψ (W X)).hasFDerivAt.comp (W X, Yb X)
          (hasFDerivAt_fst : HasFDerivAt (fun z : SeqL2 × ℝ => z.1)
            (ContinuousLinearMap.fst ℝ SeqL2 ℝ) (W X, Yb X))
      change fderiv ℝ ((fun z : SeqL2 × ℝ => z.2) *
        (fun z => ψ z.1)) (W X, Yb X) (0, 1) = _
      rw [(h1.mul h2).fderiv]
      simp [ztest, smul_eq_mul]
    simp only [hcoord, hsecond] at hform
    have hL : ∀ f : Euc p.d → ℝ,
        s45_L N f X (fun i => gradient χ (X i)) =
          Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient f x⟫) := by
      intro f
      exact S99.s99_L_chi hN1 (ψ := f) (χ := χ) X
    simp_rw [hL] at hform
    dsimp [g, Yb, W]
    have hscale :
        (∑' l, (Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
            (s45_Yi N b (HRS.Whole.pair ν b) X * pd ψ l (featureVec φ ν X))) +
          Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient b x⟫) * ψ (featureVec φ ν X) =
        (p.γ * Real.sqrt N) *
          ((∑' l, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
              (s45_Yi N b (HRS.Whole.pair ν b) X * pd ψ l (featureVec φ ν X))) +
            (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χ x, gradient b x⟫) *
              ψ (featureVec φ ν X))) := by
          have hfeat :
              (∑' l, (Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
                  (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
                (s45_Yi N b (HRS.Whole.pair ν b) X *
                  pd ψ l (featureVec φ ν X))) =
              (p.γ * Real.sqrt N) *
                (∑' l, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
                    (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
                  (s45_Yi N b (HRS.Whole.pair ν b) X *
                    pd ψ l (featureVec φ ν X))) := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro l
            field_simp [hγ.ne']
          have hbscale :
              Real.sqrt N * HRS.Whole.pair (HRS.Whole.empirical X)
                  (fun x => ⟪gradient χ x, gradient b x⟫) *
                ψ (featureVec φ ν X) =
              (p.γ * Real.sqrt N) *
                (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
                    (fun x => ⟪gradient χ x, gradient b x⟫) *
                  ψ (featureVec φ ν X)) := by
            field_simp [hγ.ne']
          rw [hfeat, hbscale]
          ring
    exact hform.trans hscale
  have hderivIntegral :
      ∫ X, fderiv ℝ T X (fun i => gradient χ (X i)) ∂(r26t3_Q R N) =
        (p.γ * Real.sqrt N) *
          ((∑' l, ∫ X, g l X ∂(r26t3_Q R N)) +
            ∫ X, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χ x, gradient b x⟫) * ψ (W X))
              ∂(r26t3_Q R N)) := by
    have hdirFun : (fun X => fderiv ℝ T X (fun i => gradient χ (X i))) =
      (fun X => (p.γ * Real.sqrt N) *
        ((∑' l, g l X) + (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient b x⟫) * ψ (W X)))) := by
      funext X
      exact hdir X
    rw [hdirFun]
    rw [integral_const_mul, integral_add hsumInt hgbInt, ← hseries]
  have hleft :
      ∫ X, s45_Yi N u (HRS.Whole.pair ν u) X * T X ∂(r26t3_Q R N) =
        Real.sqrt N * ∫ X,
          (HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair ν u) * T X ∂(r26t3_Q R N) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp [T, Yb, s45_Yi]
    ring
  have henergy :
      ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair ν u) * T X ∂(r26t3_Q R N) =
        (p.γ * (N : ℝ))⁻¹ *
          ∫ X, fderiv ℝ T X (fun i => gradient χ (X i)) ∂(r26t3_Q R N) -
        ∫ X, (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X
            (r26t3_mu R 0) -
          ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y
            (r26t3_mu R 0) ∂(r26t3_Q R N)) * T X ∂(r26t3_Q R N) := by
    simpa [ν, T] using hstein
  have hfactor : Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ *
      (p.γ * Real.sqrt N)) = 1 := by
    have hsqr : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
    field_simp [hγ.ne', hNne]
    nlinarith [hsqr]
  rw [hleft, henergy, hderivIntegral]
  simp only [T, Yb, W, g, ν]
  let S : ℝ := ∑' l, ∫ X,
    (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
      (s45_Yi N b (HRS.Whole.pair (r26t3_marg R N) b) X *
        pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)
  let C : ℝ := ∫ X,
    (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
      ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y
        (r26t3_mu R 0) ∂(r26t3_Q R N)) *
      (s45_Yi N b (HRS.Whole.pair (r26t3_marg R N) b) X *
        ψ (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)
  let D : ℝ := ∫ X,
    (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χ x, gradient b x⟫)) *
      ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)
  change Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ *
      ((p.γ * Real.sqrt N) * (S + D)) - C) = -Real.sqrt N * C + S + D
  calc Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ *
        ((p.γ * Real.sqrt N) * (S + D)) - C)
      = (Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ * (p.γ * Real.sqrt N))) *
          (S + D) - Real.sqrt N * C := by ring
    _ = S + D - Real.sqrt N * C := by rw [hfactor, one_mul]
    _ = -Real.sqrt N * C + S + D := by ring

#print axioms fp81s21_initial_E1b

end HRS.Fp81.S21

end
