import HRS.MS.Fp81S21InitialCoord
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

/-- The initial susceptibility covariance is the reference-measure average of `wF`. -/
theorem fp81s21_initialCf_pair
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (j k : ℕ) :
    fp81s21_initialCf R (φ j) (φ k) =
      HRS.Whole.pair (r26t3_mu R 0) (InitialFamData.wF F j k) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hd2 : (p.d : ℝ) / 2 ≤ (p.d : ℝ) := by nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  haveI hμdens : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact hμdens
  have hχ := F.feat hγ j
  have hφj : ContDiff ℝ 1 (φ k) := (hφ.1 k).1.of_le (by exact_mod_cast hJ)
  have hBφ : ∀ x, |φ k x| ≤ cbNorm (fp81s21_J1 p.d) (φ k) := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x
    rwa [Real.norm_eq_abs] at h
  have hDφ : ∀ x, ‖fderiv ℝ (φ k) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ k) :=
    fun x => S45.s45_cb_deriv_le hJ (hφ.1 k) x
  have hcov := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
    hχ.smooth hχ.B1 hχ.B2
    (HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 j)) hχ.r2 hχ.corr hφj
    (Bφ := cbNorm (fp81s21_J1 p.d) (φ k)) hBφ
    (Dφ := cbNorm (fp81s21_J1 p.d) (φ k)) hDφ
  calc
    fp81s21_initialCf R (φ j) (φ k) =
        p.γ⁻¹ * ∫ x, ⟪gradient (F.χ j) x, gradient (φ k) x⟫
          ∂(r26t3_mu R 0) := by
            simpa only [fp81s21_initialCf, r26t3_mu] using hcov
    _ = HRS.Whole.pair (r26t3_mu R 0) (InitialFamData.wF F j k) := by
          unfold HRS.Whole.pair InitialFamData.wF
          rw [← integral_const_mul]

/-- Summable initial covariance coefficients, with the uniform response bound from `InitialFamData`. -/
theorem fp81s21_initialCf_summable
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    Summable fun q : ℕ × ℕ =>
      ‖fp81s21_initialCf R (φ q.1) (φ q.2)‖ := by
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  let C : ℝ := (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d) *
    (p.γ⁻¹ * F.K)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply mul_nonneg
    · positivity
    · exact mul_nonneg (inv_nonneg.2 hγ.le) F.hK
  have hs : Summable b := hφ.2
  have hnn : (0 : ℕ → ℝ) ≤ b := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbb : Summable fun q : ℕ × ℕ => b q.1 * b q.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hs hs hnn hnn
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) (hbb.mul_left C)
  have hbound := fp81s21_initialCf_pair E hγ hφ F q.1 q.2
  have hw := fp81s21_initial_wF_cb hφ.1 F hγ q.1 q.2
  haveI hμdens : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := by
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact hμdens
  have hpair : |HRS.Whole.pair (r26t3_mu R 0) (InitialFamData.wF F q.1 q.2)| ≤
      cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F q.1 q.2) := by
    apply HRS.MS.Tc5.tc5_pair_le
    intro x
    exact HRS.MS.Tc5.tc5_cb_sup_le hw.1 x
  calc
    ‖fp81s21_initialCf R (φ q.1) (φ q.2)‖ =
        |fp81s21_initialCf R (φ q.1) (φ q.2)| := Real.norm_eq_abs _
    _ = |HRS.Whole.pair (r26t3_mu R 0) (InitialFamData.wF F q.1 q.2)| := by rw [hbound]
    _ ≤
        cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F q.1 q.2) := hpair
    _ ≤ (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K * b q.1)) * b q.2 := by
          simpa [b] using hw.2
    _ = C * (b q.1 * b q.2) := by dsimp [C]; ac_rfl

/-- Generic pointwise Stein expansion for a centered Gaussian sequence with summable covariance. -/
theorem fp81s21_D1_pointwise
    {C : ℕ → ℕ → ℝ} {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G C)
    (hC : Summable fun q : ℕ × ℕ => ‖C q.1 q.2‖)
    {Φ f : SeqL2 → ℝ} (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G) (z : SeqL2) :
    Φ z - ∫ z', Φ z' ∂G =
      (∑' q : ℕ × ℕ, C q.1 q.2 * pd (pd f q.1) q.2 z) -
        ∑' j, SeqL2.coord z j * pd f j z := by
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
  have h := hst z
  rw [S99.s99_contraction hG hC hf2 z, S99.s99_euler] at h
  have hsm : Summable fun q : ℕ × ℕ => C q.1 q.2 * pd (pd f q.1) q.2 z := by
    refine Summable.of_norm_bounded hC fun q => ?_
    rw [norm_mul]
    have h1 : |pd (pd f q.1) q.2 z| ≤ 1 := ((hf.pd q.1).pd q.2).abs_le z
    calc ‖C q.1 q.2‖ * ‖pd (pd f q.1) q.2 z‖ ≤ ‖C q.1 q.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact h1) (norm_nonneg _)
      _ = ‖C q.1 q.2‖ := mul_one _
  have heq :
      ∑' j, ∑' k, C j k *
          fderiv ℝ (fderiv ℝ f) z (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) =
        ∑' q : ℕ × ℕ, C q.1 q.2 * pd (pd f q.1) q.2 z := by
    rw [hsm.tsum_prod]
    refine tsum_congr fun j => tsum_congr fun k => ?_
    rw [S99.s99_pd_pd hf2]
  rw [heq] at h
  exact h.symm

/-- The nonthermal S9.9 expansion at the actual initial preparation law. -/
theorem fp81s21_initial_D1
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => fp81s21_initialCf R (φ i) (φ j)))
    {Φ f : SeqL2 → ℝ} (hΦc : Continuous Φ) {CΦ : ℝ}
    (hΦb : ∀ z, |Φ z| ≤ CΦ) (hf : SteinCl f)
    (hst : ∀ x, ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂G - fderiv ℝ f x x =
      Φ x - ∫ z, Φ z ∂G) {N : ℕ} (hN : 2 ≤ N) :
    ∫ X, Φ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) - ∫ z, Φ z ∂G =
      (∑' q : ℕ × ℕ, ∫ X,
        (fp81s21_initialCf R (φ q.1) (φ q.2) -
          HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F q.1 q.2)) *
          pd (pd f q.1) q.2 (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) +
        ∑' j, ∫ X,
          (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) *
            pd f j (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  let P := r26t3_Q R N
  let ν := r26t3_marg R N
  haveI hP : IsProbabilityMeasure P := by
    dsimp [P]
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  have hWc : Continuous W := (S99.s99_W_contDiff hN1 hJ hφ).continuous
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hs1 : Summable b := hφ.2
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbsq : Summable fun q : ℕ × ℕ => b q.1 * b q.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hs1 hs1 hb0 hb0
  let C : ℕ → ℕ → ℝ := fun j k => fp81s21_initialCf R (φ j) (φ k)
  have hCs : Summable fun q : ℕ × ℕ => ‖C q.1 q.2‖ :=
    fp81s21_initialCf_summable E hγ hφ F
  change IsCenteredGaussianSeq G C at hG
  have hD1pt := fp81s21_D1_pointwise hG hCs hf hst
  let g : ℕ × ℕ → SeqL2 → ℝ := fun q z => pd (pd f q.1) q.2 z
  have hg_cont : ∀ q, Continuous (g q) := fun q => S99.s99_pdpd_cont hf q.1 q.2
  have hg_bd : ∀ q z, |g q z| ≤ 1 := fun q z => ((hf.pd q.1).pd q.2).abs_le z
  have hpd_bd : ∀ j z, |pd f j z| ≤ 1 := fun j z => (hf.pd j).abs_le z
  let Fi : (ℕ × ℕ) ⊕ ℕ → EucConfig p.d N → ℝ := Sum.elim
    (fun q X => C q.1 q.2 * g q (W X))
    (fun j X => -(SeqL2.coord (W X) j * pd f j (W X)))
  let Mi : (ℕ × ℕ) ⊕ ℕ → ℝ := Sum.elim
    (fun q => ‖C q.1 q.2‖) (fun j => 2 * Real.sqrt N * b j)
  have hM1 : Summable (Mi ∘ Sum.inl) := hCs
  have hM2 : Summable (Mi ∘ Sum.inr) := hs1.mul_left (2 * Real.sqrt N)
  have hMs : Summable Mi := Summable.sum Mi hM1 hM2
  have hmeas : ∀ i, AEStronglyMeasurable (Fi i) P := by
    intro i
    rcases i with q | j
    · exact (continuous_const.mul ((hg_cont q).comp hWc)).aestronglyMeasurable
    · exact (((S45.s45_coord_continuous j).comp hWc).mul
        ((S99.s99_pd_cont hf j).comp hWc)).neg.aestronglyMeasurable
  have hbd : ∀ i X, |Fi i X| ≤ Mi i := by
    intro i X
    rcases i with q | j
    · simp only [Fi, Mi, Sum.elim_inl]
      rw [abs_mul, ← Real.norm_eq_abs (C q.1 q.2)]
      calc ‖C q.1 q.2‖ * |g q (W X)| ≤ ‖C q.1 q.2‖ * 1 :=
            mul_le_mul_of_nonneg_left (hg_bd q _) (norm_nonneg _)
        _ = _ := mul_one _
    · simp only [Fi, Mi, Sum.elim_inr, abs_neg]
      rw [abs_mul]
      calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
            mul_le_mul (S99.s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
              have := hb0 j
              positivity)
        _ = _ := mul_one _
  have h1 := @fp81s21_integral_tsum ((ℕ × ℕ) ⊕ ℕ) (EucConfig p.d N)
    (inferInstance : Countable ((ℕ × ℕ) ⊕ ℕ))
    (inferInstance : MeasurableSpace (EucConfig p.d N)) P hP Fi Mi hMs hmeas hbd
  have hpt : ∀ X : EucConfig p.d N,
      ∑' i, Fi i X = Φ (W X) - ∫ z, Φ z ∂G := by
    intro X
    have hs1' : Summable fun q : ℕ × ℕ => Fi (Sum.inl q) X := by
      refine Summable.of_norm_bounded hCs fun q => ?_
      simp only [Fi, Sum.elim_inl, norm_mul]
      calc ‖C q.1 q.2‖ * ‖g q (W X)‖ ≤ ‖C q.1 q.2‖ * 1 :=
            mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd q _) (norm_nonneg _)
        _ = _ := mul_one _
    have hs2' : Summable fun j : ℕ => Fi (Sum.inr j) X := by
      refine Summable.of_norm_bounded (hs1.mul_left (2 * Real.sqrt N)) fun j => ?_
      simp only [Fi, Sum.elim_inr, norm_neg, norm_mul]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
            mul_le_mul (S99.s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
              have := hb0 j
              positivity)
        _ = _ := by rw [mul_one]
    rw [Summable.tsum_sum (f := fun i => Fi i X) hs1' hs2']
    have h := hD1pt (W X)
    rw [h]
    simp only [Fi, Sum.elim_inl, Sum.elim_inr, tsum_neg]
    ring
  have hint_pt :
      ∫ X, ∑' i, Fi i X ∂P = ∫ X, Φ (W X) ∂P - ∫ z, Φ z ∂G := by
    simp_rw [hpt]
    have hΦW : Integrable (fun X : EucConfig p.d N => Φ (W X)) P :=
      Integrable.of_bound (hΦc.comp hWc).aestronglyMeasurable CΦ
        (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hΦb _)
    rw [integral_sub hΦW (integrable_const _), integral_const]
    simp
  have hIbase :
      ∫ X, Φ (W X) ∂P - ∫ z, Φ z ∂G =
        (∑' q : ℕ × ℕ, ∫ X, C q.1 q.2 * g q (W X) ∂P) -
          ∑' j, ∫ X, SeqL2.coord (W X) j * pd f j (W X) ∂P := by
    rw [← hint_pt, ← h1]
    have hI1 : Summable fun q : ℕ × ℕ => ∫ X, Fi (Sum.inl q) X ∂P := by
      refine Summable.of_norm_bounded hCs fun q => ?_
      have h := norm_integral_le_of_norm_le_const (μ := P)
        (f := fun X : EucConfig p.d N => Fi (Sum.inl q) X)
        (C := ‖C q.1 q.2‖) (Filter.Eventually.of_forall fun X => by
          change ‖C q.1 q.2 * g q (W X)‖ ≤ ‖C q.1 q.2‖
          rw [norm_mul]
          calc ‖C q.1 q.2‖ * ‖g q (W X)‖ ≤ ‖C q.1 q.2‖ * 1 :=
                mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd q _) (norm_nonneg _)
            _ = _ := mul_one _)
      simpa [Fi] using h
    have hI2 : Summable fun j : ℕ => ∫ X, Fi (Sum.inr j) X ∂P := by
      refine Summable.of_norm_bounded (hs1.mul_left (2 * Real.sqrt N)) fun j => ?_
      have h := norm_integral_le_of_norm_le_const (μ := P)
        (f := fun X : EucConfig p.d N => Fi (Sum.inr j) X)
        (C := 2 * Real.sqrt N * b j) (Filter.Eventually.of_forall fun X => by
          change ‖-(SeqL2.coord (W X) j * pd f j (W X))‖ ≤ 2 * Real.sqrt N * b j
          rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
                mul_le_mul (S99.s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
                  have := hb0 j
                  positivity)
            _ = _ := by rw [mul_one])
      simpa [Fi] using h
    rw [Summable.tsum_sum (f := fun i => ∫ X, Fi i X ∂P) hI1 hI2]
    simp only [Fi, Sum.elim_inl, Sum.elim_inr]
    rw [tsum_congr fun j => integral_neg _, tsum_neg]
    ring
  let Tint : ℕ × ℕ → ℝ := fun q =>
    ∫ X, fp81s21_initial_wF_integrand F f N q.1 q.2 X ∂P
  let Aint : ℕ → ℝ := fun j =>
    ∫ X, (fp81s21_initialBq R (F.χ j) N X / Real.sqrt N) * pd f j (W X) ∂P
  let Zint : ℕ → ℝ := fun j =>
    ∫ X, SeqL2.coord (W X) j * pd f j (W X) ∂P
  let Cint : ℕ × ℕ → ℝ := fun q => ∫ X, C q.1 q.2 * g q (W X) ∂P
  let bResp : ℝ := (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d) *
    (p.γ⁻¹ * F.K)
  have hbResp : 0 ≤ bResp := by
    dsimp [bResp]
    exact mul_nonneg (by positivity) (mul_nonneg (inv_nonneg.2 hγ.le) F.hK)
  have hbRespSum : Summable fun q : ℕ × ℕ => bResp * (b q.1 * b q.2) :=
    hbsq.mul_left bResp
  have hTintMeas : ∀ (q : ℕ × ℕ), AEStronglyMeasurable
      (fun X : EucConfig p.d N => fp81s21_initial_wF_integrand F f N q.1 q.2 X) P := by
    intro q
    exact fp81s21_initial_wF_measurable hγ hφ F hf hN hP q.1 q.2
  have hTintBound : ∀ (q : ℕ × ℕ) (X : EucConfig p.d N),
      |fp81s21_initial_wF_integrand F f N q.1 q.2 X| ≤ bResp * (b q.1 * b q.2) := by
    intro q X
    calc
      |fp81s21_initial_wF_integrand F f N q.1 q.2 X| =
          |HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F q.1 q.2)| *
            |pd (pd f q.1) q.2 (featureVec φ (r26t3_marg R N) X)| := by
        rw [fp81s21_initial_wF_integrand, abs_mul]
      _ ≤ (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
            (p.γ⁻¹ * F.K)) * (b q.1 * b q.2) := by
        simpa [b] using fp81s21_initial_wF_integrand_bound hγ hφ F hf hN1 q.1 q.2 X
      _ = bResp * (b q.1 * b q.2) := by dsimp [bResp]
  have hTintIntegrable : ∀ (q : ℕ × ℕ), Integrable
      (fun X : EucConfig p.d N => fp81s21_initial_wF_integrand F f N q.1 q.2 X) P := by
    intro q
    refine Integrable.of_bound (hTintMeas q) (bResp * (b q.1 * b q.2))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact hTintBound q X
  have hTsum : Summable Tint := by
    refine Summable.of_norm_bounded hbRespSum fun q => ?_
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => fp81s21_initial_wF_integrand F f N q.1 q.2 X)
      (C := bResp * (b q.1 * b q.2))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hTintBound q X)
    simpa using h
  have hRows : Summable fun j : ℕ => ∑' k, Tint (j, k) := hTsum.prod
  have hCsum : Summable Cint := by
    refine Summable.of_norm_bounded hCs fun q => ?_
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => C q.1 q.2 * g q (W X))
      (C := ‖C q.1 q.2‖) (Filter.Eventually.of_forall fun X => by
        rw [norm_mul]
        calc ‖C q.1 q.2‖ * ‖g q (W X)‖ ≤ ‖C q.1 q.2‖ * 1 :=
              mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd q _) (norm_nonneg _)
          _ = _ := mul_one _)
    simpa using h
  have hZsum : Summable Zint := by
    refine Summable.of_norm_bounded (hs1.mul_left (2 * Real.sqrt N)) fun j => ?_
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => SeqL2.coord (W X) j * pd f j (W X))
      (C := 2 * Real.sqrt N * b j) (Filter.Eventually.of_forall fun X => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |SeqL2.coord (W X) j| * |pd f j (W X)| ≤ (2 * Real.sqrt N * b j) * 1 :=
              mul_le_mul (S99.s99_Wc_bound hN1 hφ j X) (hpd_bd j _) (abs_nonneg _) (by
                have := hb0 j
                positivity)
          _ = _ := by rw [mul_one])
    simpa using h
  have hcoord : ∀ j, Zint j = -Aint j + ∑' k, Tint (j, k) := by
    intro j
    simpa only [Zint, Aint, Tint, W, ν, P, fp81s21_initial_wF_integrand] using
      fp81s21_initial_coord_identity E hγ hφ F hf hN j
  have hAeq : ∀ j, Aint j = (∑' k, Tint (j, k)) - Zint j := by
    intro j
    rw [hcoord j]
    ring
  have hAsum : Summable fun j : ℕ => Aint j := by
    refine (hRows.sub hZsum).congr fun j => ?_
    exact (hAeq j).symm
  have hS2 :
      (∑' j, Zint j) = -(∑' j, Aint j) + ∑' q : ℕ × ℕ, Tint q := by
    simp_rw [hcoord]
    rw [hAsum.neg.tsum_add hRows, tsum_neg, hTsum.tsum_prod]
  have hsplit : ∀ q : ℕ × ℕ, ∫ X,
      (C q.1 q.2 - HRS.Whole.pair (HRS.Whole.empirical X)
        (InitialFamData.wF F q.1 q.2)) * g q (W X) ∂P = Cint q - Tint q := by
    intro q
    have hCg : Integrable (fun X : EucConfig p.d N => C q.1 q.2 * g q (W X)) P :=
      Integrable.of_bound (continuous_const.mul ((hg_cont q).comp hWc)).aestronglyMeasurable
        (‖C q.1 q.2‖) (Filter.Eventually.of_forall fun X => by
          rw [norm_mul]
          calc ‖C q.1 q.2‖ * ‖g q (W X)‖ ≤ ‖C q.1 q.2‖ * 1 :=
                mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hg_bd q _) (norm_nonneg _)
            _ = _ := mul_one _)
    rw [← integral_sub hCg (hTintIntegrable q)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [Cint, Tint, fp81s21_initial_wF_integrand]
    ring
  have hS1 :
      (∑' q : ℕ × ℕ, ∫ X,
        (C q.1 q.2 - HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F q.1 q.2)) * g q (W X) ∂P) =
        (∑' q : ℕ × ℕ, Cint q) - ∑' q : ℕ × ℕ, Tint q := by
    simp_rw [hsplit]
    rw [hCsum.tsum_sub hTsum]
  rw [hIbase, hS2]
  show _ =
      (∑' q : ℕ × ℕ, ∫ X,
        (C q.1 q.2 - HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F q.1 q.2)) * g q (W X) ∂P) +
        ∑' j, Aint j
  rw [hS1]
  ring

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCf_pair
#print axioms HRS.Fp81.S21.fp81s21_initialCf_summable
#print axioms HRS.Fp81.S21.fp81s21_D1_pointwise
#print axioms HRS.Fp81.S21.fp81s21_initial_D1
