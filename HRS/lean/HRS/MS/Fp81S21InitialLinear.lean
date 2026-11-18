import HRS.MS.Fp81S21InitialUncentered12
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

/-!
## SOL31 packet 24a: arbitrary-observable linear response

Thermal source contracts (exact normalizations):

* `S99.s99_chi1` (`R2SeAux16:40`) chooses `K₂ ≥ 0` before `w`; for every
  `w : Euc d → ℝ` with `MemCb (k0 d) w`, it returns `χ ∈ C²` with
  `S46.S46Feat d s a β γ w χ (K₂ * cbNorm (k0 d) w)` and the pointwise equation
  `thermalGen d s a β χ = γ * aRep d s a β γ w`.
* `S99.s99_E1_plain` (`R2SeAux9:81`) has left side
  `E[s45_Yi N w (pair ν w) X * ψ(featureVec φ ν X)]`; its right side is
  `E[(√N * s45_Rp μ ν P (commutatorKernel d s (gradient χ)) X) * ψ(featureVec φ ν X)]`
  plus `∑' l, E[(γ⁻¹ * pair (empirical X) (gradient χ · gradient (φ l))) *
  pd ψ l (featureVec φ ν X)]`.

Dependency classification: `S99.s99_fderivF_apply`, `S99.s99_L_chi`, and
`fp81s21_integral_tsum` are **generic**; `initial_stein_pairEnergy`,
`fp81s21_s47_Rp_eq`, `InitialSteinEnv`, `InitialFamData`, the actual-law
normalizations, and the S48 biases are **already ported**; the thermal S46
Stein equation is **thermal-only** and is replaced by the S47 equation at
`R.ρ 0`. The response is recorded a.e. because `S47Feat` is an L² corrector
contract; the thermal pointwise representative equality is not needed by the
linear consumers.
-/

/-- Order-one S47 correctors for every `C_b^{k0}` observable at the actual
initial density. The same witness is identified in L² with the actual response
representative, so its generator normalization is `weightedGen χ = γ a_R(w)` a.e. -/
theorem fp81s21_initial_orderOne_corrector
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ w : Euc p.d → ℝ, MemCb (fp81s21_k0 p.d) w →
      ∃ χ : Euc p.d → ℝ,
        ContDiff ℝ 2 χ ∧
        S47.S47Feat p.d p.s (R.ρ 0) p.γ w χ
          (K₂ * cbNorm (fp81s21_k0 p.d) w) ∧
        (∀ᵐ x ∂(r26t3_mu R 0), weightedGen (R.ρ 0) χ x =
          p.γ * r26t3_a R w x) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  have hJ : (p.d : ℝ) / 2 + 2 < (fp81s21_k0 p.d : ℝ) := by
    unfold fp81s21_k0
    push_cast
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg p.d
    linarith
  have hU := s21f_unifref_init p hδ hδh R
  obtain ⟨E⟩ := initialSteinEnv_exists hδ hδh R hγ
  obtain ⟨K₂, hK₂, hcorrect⟩ := S47.s47_corrector_unif p.hd p.hs0 hsd
    (fp81s21_k0 p.d) hJ p.a p.a p.β p.β p.γ p.γ p.ha p.hβ hγ δ
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c, S, hc, hTc⟩ := href 0
  refine ⟨K₂, hK₂, fun w hw => ?_⟩
  obtain ⟨χ, hχ⟩ := hcorrect p.a ⟨le_rfl, le_rfl⟩ p.β ⟨le_rfl, le_rfl⟩
    p.γ ⟨le_rfl, le_rfl⟩ (R.ρ 0) hU w hw
  refine ⟨χ, hχ.smooth, hχ, ?_⟩
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let r : Euc p.d → ℝ := fun x => p.γ⁻¹ * weightedGen (R.ρ 0) χ x
  haveI hμ : IsProbabilityMeasure μ := by
    dsimp [μ, r26t3_mu]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hzero : ∫ x, weightedGen (R.ρ 0) χ x ∂μ = 0 := by
    exact fp81s21_initial_integral_weightedGen_zero E.reference hχ.smooth hχ.B1 hχ.B2
  have hrLp : MemLp r 2 μ := by
    simpa [r, μ, r26t3_mu] using hχ.r2.const_mul p.γ⁻¹
  have hrMean : ∫ x, r x ∂μ = 0 := by
    simp only [r, integral_const_mul, hzero, mul_zero]
  have hrZero : MemL2Zero μ r := ⟨hrLp, hrMean⟩
  have hresp : HRS.Whole.IsResponse (rieszKernel p.d p.s) μ p.γ w r := by
    refine ⟨hrZero, ?_⟩
    have hKsmul : HRS.Whole.Kop (rieszKernel p.d p.s) μ r =
        fun x => p.γ⁻¹ * HRS.Whole.Kop (rieszKernel p.d p.s) μ
          (weightedGen (R.ρ 0) χ) x := by
      funext x
      exact HRS.MS.S98.s98_kop_smul (rieszKernel p.d p.s) μ p.γ⁻¹
        (weightedGen (R.ρ 0) χ) x
    filter_upwards [hχ.corr] with x hx
    have hx' : p.γ⁻¹ * weightedGen (R.ρ 0) χ x +
        HRS.Whole.Kop (rieszKernel p.d p.s) μ (weightedGen (R.ρ 0) χ) x =
        HRS.Whole.projMean μ w x := by
      have hx0 := hx
      unfold HRS.Whole.susceptibilityOp at hx0
      simpa [μ, r26t3_mu] using hx0
    change r x + p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) μ r x =
      HRS.Whole.projMean μ w x
    rw [hKsmul]
    dsimp [r]
    calc p.γ⁻¹ * weightedGen (R.ρ 0) χ x +
          p.γ * (p.γ⁻¹ * HRS.Whole.Kop (rieszKernel p.d p.s) μ
            (weightedGen (R.ρ 0) χ) x) =
          p.γ⁻¹ * weightedGen (R.ρ 0) χ x +
            HRS.Whole.Kop (rieszKernel p.d p.s) μ (weightedGen (R.ρ 0) χ) x := by
              rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]
      _ = HRS.Whole.projMean μ w x := hx'
  have hinv : HRS.Whole.IsResponse (rieszKernel p.d p.s) μ p.γ w
      (HRS.Whole.responseInverse (rieszKernel p.d p.s) μ p.γ w) := by
    unfold HRS.Whole.responseInverse
    rw [dif_pos ⟨r, hresp⟩]
    exact Classical.choose_spec (⟨r, hresp⟩ :
      ∃ v, HRS.Whole.IsResponse (rieszKernel p.d p.s) μ p.γ w v)
  have huniq := HRS.MS.S98.s98_resp_unique (by have : 2 ≤ p.d := p.hd; omega)
    p.hs0 hsd hc hTc hγ hinv hresp
  have hrep := r26t3_response_ae hδ hδh R w
    (HRS.MS.Tc5.tc5_memLp_of_cb hw)
  have hEq : r26t3_a R w =ᵐ[μ] r := hrep.trans huniq
  filter_upwards [hEq] with x hx
  rw [hx]
  dsimp [r]
  field_simp [hγ.ne']

/-- The arbitrary-observable plain Stein response at the actual initial law.
The first term is written with the exactly centered pair energy; by
`fp81s21_s47_Rp_eq` it is the S47 remainder `√N * Rp` used in the thermal
`s99_E1_plain` contract. -/
theorem fp81s21_initial_plain_response
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {w χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hw : MemCb (fp81s21_k0 p.d) w)
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ w χ Bχ)
    {ψ : SeqL2 → ℝ} (hψ : Bd 1 ψ) :
    ∫ X, s45_Yi N w (HRS.Whole.pair (r26t3_marg R N) w) X *
        ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) =
      -(Real.sqrt N) * ∫ X,
          (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
            ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y
              (r26t3_mu R 0) ∂(r26t3_Q R N)) *
          ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) +
        ∑' l, ∫ X,
          (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
            pd ψ l (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hν : IsProbabilityMeasure (r26t3_marg R N) := s99_nu_prob hN1
  letI : IsProbabilityMeasure (r26t3_marg R N) := hν
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  let T : EucConfig p.d N → ℝ := fun X => ψ (W X)
  have hWcd : ContDiff ℝ 1 W := s99_W_contDiff hN1 hJ hφ
  have hWc : Continuous W := hWcd.continuous
  have hTcd : ContDiff ℝ 1 T := hψ.1.comp hWcd
  have hTbound : ∀ X, |T X| ≤ 1 := by
    intro X
    have hx := hψ.abs_le (W X)
    simpa [T] using hx
  have hbs : Summable (fun l : ℕ => cbNorm (fp81s21_J1 p.d) (φ l)) := hφ.2
  let b : ℕ → ℝ := fun l => cbNorm (fp81s21_J1 p.d) (φ l)
  let Csum : ℝ := Real.sqrt N * ∑' l, b l
  have hb0 : ∀ l, 0 ≤ b l := fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hCsum0 : 0 ≤ Csum := by
    dsimp [Csum]
    exact mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg hb0)
  have hCLMsum : ∀ X : EucConfig p.d N,
      Summable (fun l : ℕ =>
        (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) := by
    intro X
    exact Summable.of_norm_bounded (hbs.mul_left (Real.sqrt N))
      (fun l => s99_Wterm_fderiv_norm hN1 hJ hφ.1 l X)
  have hTderiv : ∀ X, ‖fderiv ℝ T X‖ ≤ Csum := by
    intro X
    have hWder := s99_W_hasFDerivAt (ν := ν) hN1 hJ hφ X
    have hchain := (hψ.1.differentiable one_ne_zero (W X)).hasFDerivAt.comp X hWder
    refine ContinuousLinearMap.opNorm_le_bound _ hCsum0 fun u => ?_
    change ‖fderiv ℝ (fun Y : EucConfig p.d N => ψ (W Y)) X u‖ ≤
      Csum * ‖u‖
    change ‖fderiv ℝ (ψ ∘ W) X u‖ ≤ Csum * ‖u‖
    rw [hchain.fderiv]
    change ‖fderiv ℝ ψ (W X)
        ((∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u)‖ ≤
      Csum * ‖u‖
    have hLnorm : Summable fun l : ℕ =>
        ‖(s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
        (hbs.mul_left (Real.sqrt N))
      exact s99_Wterm_fderiv_norm hN1 hJ hφ.1 l X
    have hsumNorm :
        ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ ≤ Csum := by
      calc ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖
          ≤ ∑' l, ‖(s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ :=
            norm_tsum_le_tsum_norm hLnorm
        _ ≤ ∑' l, Real.sqrt N * b l :=
          Summable.tsum_le_tsum (fun l => s99_Wterm_fderiv_norm hN1 hJ hφ.1 l X)
            hLnorm (hbs.mul_left (Real.sqrt N))
        _ = Csum := by
          dsimp [Csum]
          rw [← tsum_mul_left]
    have hsumV :
        ‖(∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u‖ ≤
          Csum * ‖u‖ := by
      calc ‖(∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u‖
          ≤ ‖∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))‖ * ‖u‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ Csum * ‖u‖ := mul_le_mul_of_nonneg_right hsumNorm (norm_nonneg _)
    have hDψ : ‖fderiv ℝ ψ (W X)‖ ≤ 1 := hψ.fderiv_le (W X)
    calc ‖fderiv ℝ ψ (W X)
          ((∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u)‖
        ≤ ‖fderiv ℝ ψ (W X)‖ *
            ‖(∑' l, (s45_L N (φ l) X).smulRight (s45_e1 l (1 : ℝ))) u‖ :=
          (fderiv ℝ ψ (W X)).le_opNorm _
      _ ≤ 1 * (Csum * ‖u‖) := mul_le_mul hDψ hsumV (norm_nonneg _) zero_le_one
      _ = Csum * ‖u‖ := one_mul _
  have hχ1 : MemCb 1 w :=
    (HRS.MS.Tc5.tc5_cb_mono (m := 1) (J := fp81s21_k0 p.d)
      (by have := fp81s21_k0_ge_one p.d; omega) hw).1
  have hstein := initial_stein_pairEnergy E hγ hN hχ hχ1 hTcd
    (BF := 1) hTbound (DF := Csum) hTderiv
  let b0 : Euc p.d → ℝ := fun _ => 0
  have hb0mem : MemCb (fp81s21_J1 p.d) b0 :=
    (HRS.MS.Tc5.tc5_cb_const (d := p.d) (fp81s21_J1 p.d) 0).1
  let Ψ : SeqL2 × ℝ → ℝ := fun z => ψ z.1
  have hΨ : ContDiff ℝ 1 Ψ := hψ.1.comp contDiff_fst
  have hΨderiv (z : SeqL2) :
      fderiv ℝ Ψ (z, 0) =
        (fderiv ℝ ψ z).comp (ContinuousLinearMap.fst ℝ SeqL2 ℝ) := by
    have hdψ : Differentiable ℝ ψ := hψ.1.differentiable one_ne_zero
    exact ((hdψ z).hasFDerivAt.comp (z, 0)
      (hasFDerivAt_fst : HasFDerivAt (fun q : SeqL2 × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ SeqL2 ℝ) (z, 0))).fderiv
  have hΨcoord : ∀ l z,
      fderiv ℝ Ψ (z, 0) (s45_e1 l (1 : ℝ), 0) = pd ψ l z := by
    intro l z
    rw [hΨderiv z]
    rfl
  have hΨsecond : ∀ z,
      fderiv ℝ Ψ (z, 0) (0, 1) = 0 := by
    intro z
    rw [hΨderiv z]
    simp
  have hderivFormula : ∀ X,
      fderiv ℝ T X (fun i => gradient χ (X i)) =
        Real.sqrt N * ∑' l,
          HRS.Whole.pair (HRS.Whole.empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫) *
            pd ψ l (W X) := by
    intro X
    have hform := s99_fderivF_apply hN1 hJ hφ (ν := ν) (b := b0) hb0mem
      hΨ X (fun i => gradient χ (X i))
    have hZ : Zq N φ b0 ν X = (W X, 0) := by
      have hpairν : HRS.Whole.pair ν b0 = 0 := by simp [b0, HRS.Whole.pair]
      have hpairEmp : HRS.Whole.pair (HRS.Whole.empirical X) b0 = 0 := by
        rw [HRS.Whole.pair_empirical (by omega : 0 < N)]
        simp [b0, HRS.Whole.pair]
      simp [Zq, S99.Zq, W, b0, hpairν, hpairEmp, s45_Yi]
    rw [hZ] at hform
    simp only [hΨcoord, hΨsecond, mul_zero, add_zero] at hform
    have hform' : fderiv ℝ T X (fun i => gradient χ (X i)) =
        ∑' l, s45_L N (φ l) X (fun i => gradient χ (X i)) * pd ψ l (W X) := by
      simpa [T, W, Ψ, Zq, S99.Zq] using hform
    rw [hform', ← tsum_mul_left]
    congr 1
    funext l
    rw [S99.s99_L_chi hN1 (ψ := φ l) (χ := χ) X]
    ring_nf
  let g : ℕ → EucConfig p.d N → ℝ := fun l X =>
    (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) * pd ψ l (W X)
  let M : ℕ → ℝ := fun l => (p.γ⁻¹ * Bχ) * b l
  have hM0 : ∀ l, 0 ≤ M l := fun l =>
    mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le)
      ((norm_nonneg _).trans (hχ.B1 0))) (hb0 l)
  have hψderCont : Continuous (fderiv ℝ ψ) := hψ.1.continuous_fderiv one_ne_zero
  have hpdc : ∀ l, Continuous fun z : SeqL2 => pd ψ l z := by
    intro l
    unfold pd
    exact hψderCont.clm_apply continuous_const
  have hχ1cont : ContDiff ℝ 1 χ := hχ.smooth.of_le (by norm_num)
  have hχgrad : Continuous (gradient χ) := s45_gradient_continuous hχ1cont
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hχ.B1 0)
  have hgbound : ∀ l X, |g l X| ≤ M l := by
    intro l X
    have hgradφ := s45_cb_deriv_le hJ (hφ.1 l) 
    have hφgrad : ∀ x, ‖gradient (φ l) x‖ ≤ b l := by
      intro x
      rw [s45_norm_gradient]
      exact hgradφ x
    have hinner : ∀ x,
        |⟪gradient χ x, gradient (φ l) x⟫| ≤ Bχ * b l := by
      intro x
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hχ.B1 x) (hφgrad x) (norm_nonneg _) hBχ0)
    have hemp := s45_abs_pair_empirical_le hN1 hinner X
    have hpd : |pd ψ l (W X)| ≤ 1 := by
      unfold pd
      calc |fderiv ℝ ψ (W X) (s45_e1 l (1 : ℝ))| =
            ‖fderiv ℝ ψ (W X) (s45_e1 l (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ ψ (W X)‖ * ‖s45_e1 l (1 : ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * 1 := mul_le_mul (hψ.fderiv_le (W X))
              (by rw [s99_e1_norm]) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    simp only [g, M]
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    calc p.γ⁻¹ * |HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| *
          |pd ψ l (W X)| ≤ (p.γ⁻¹ * (Bχ * b l)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hemp (inv_nonneg.2 hγ.le))
            hpd (abs_nonneg _) (mul_nonneg (inv_nonneg.2 hγ.le)
              (mul_nonneg hBχ0 (hb0 l)))
      _ = M l := by dsimp [M]; ring
  have hgintegrable : ∀ l, AEStronglyMeasurable (g l) (r26t3_Q R N) := by
    intro l
    have hφ1 : ContDiff ℝ 1 (φ l) := (hφ.1 l).1.of_le (by exact_mod_cast hJ)
    have hinnerc : Continuous fun x : Euc p.d =>
        ⟪gradient χ x, gradient (φ l) x⟫ :=
      hχgrad.inner (s45_gradient_continuous hφ1)
    have hpairm := s45_measurable_pair_empirical hN1 hinnerc.measurable
    change AEStronglyMeasurable
      (fun X => (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) * pd ψ l (W X))
      (r26t3_Q R N)
    have hmeas : Measurable (g l) := by
      have hconst : Measurable (fun _ : EucConfig p.d N => p.γ⁻¹) := measurable_const
      convert hconst.mul (hpairm.mul ((hpdc l).comp hWc).measurable) using 1
      funext X
      change (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) * pd ψ l (W X) =
        p.γ⁻¹ * (HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient (φ l) x⟫) * pd ψ l (W X))
      rw [mul_assoc]
    exact hmeas.aestronglyMeasurable
  have hsumM : Summable M := hbs.mul_left (p.γ⁻¹ * Bχ)
  have hseries := fp81s21_integral_tsum hsumM hgintegrable hgbound
  have hderivPointwise (X : EucConfig p.d N) :
      fderiv ℝ T X (fun i => gradient χ (X i)) =
        (p.γ * Real.sqrt N) * ∑' l, g l X := by
    rw [hderivFormula]
    have hsumScale :
        p.γ * ∑' l, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫) * pd ψ l (W X)) =
          ∑' l, HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫) * pd ψ l (W X) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      field_simp [hγ.ne']
    dsimp [g]
    rw [← hsumScale]
    ring
  have hderivIntegral :
      ∫ X, fderiv ℝ T X (fun i => gradient χ (X i)) ∂(r26t3_Q R N) =
        (p.γ * Real.sqrt N) *
          ∑' l, ∫ X, g l X ∂(r26t3_Q R N) := by
    calc ∫ X, fderiv ℝ T X (fun i => gradient χ (X i)) ∂(r26t3_Q R N)
        = ∫ X, (p.γ * Real.sqrt N) * ∑' l, g l X ∂(r26t3_Q R N) :=
          integral_congr_ae (Filter.Eventually.of_forall hderivPointwise)
      _ = (p.γ * Real.sqrt N) * ∫ X, ∑' l, g l X ∂(r26t3_Q R N) :=
          integral_const_mul _ _
      _ = (p.γ * Real.sqrt N) * ∑' l, ∫ X, g l X ∂(r26t3_Q R N) := by rw [← hseries]
  have hstein := initial_stein_pairEnergy E hγ hN hχ hχ1 hTcd
    (BF := 1) hTbound (DF := Csum) hTderiv
  have hleft :
      ∫ X, s45_Yi N w (HRS.Whole.pair ν w) X * T X ∂(r26t3_Q R N) =
        Real.sqrt N * ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair ν w) * T X
          ∂(r26t3_Q R N) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp [T, s45_Yi]
    ring
  have henergy :
      ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair ν w) * T X ∂(r26t3_Q R N) =
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
  simp only [T, ν, W, g]
  let S : ℝ := ∑' l, ∫ X,
    (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
      pd ψ l (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)
  let C : ℝ := ∫ X,
    (pairEnergy (commutatorKernel p.d p.s (gradient χ)) X (r26t3_mu R 0) -
      ∫ Y, pairEnergy (commutatorKernel p.d p.s (gradient χ)) Y
        (r26t3_mu R 0) ∂(r26t3_Q R N)) * ψ (featureVec φ (r26t3_marg R N) X)
      ∂(r26t3_Q R N)
  change Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ * ((p.γ * Real.sqrt N) * S) - C) =
    -Real.sqrt N * C + S
  calc Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ * ((p.γ * Real.sqrt N) * S) - C)
      = (Real.sqrt N * ((p.γ * (N : ℝ))⁻¹ * (p.γ * Real.sqrt N))) * S -
          Real.sqrt N * C := by ring
    _ = S - Real.sqrt N * C := by rw [hfactor, one_mul]
    _ = -Real.sqrt N * C + S := by ring

#print axioms fp81s21_initial_orderOne_corrector
#print axioms fp81s21_initial_plain_response

end HRS.Fp81.S21

end
