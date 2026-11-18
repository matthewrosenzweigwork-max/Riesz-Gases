import HRS.MS.Fp81S21UnifLinSeries2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- Uniform `Ylin` estimate for an indexed feature family, assuming one common feature-sum
bound and one common smooth CLT certificate. -/
theorem fp81s21_initial_Ylin_uniform_of_common_CLT
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {ι : Type} (φ : ι → ℕ → Euc p.d → ℝ)
    (hφ : ∀ i, IsSummableFeatureFamily (fp81s21_J1 p.d) (φ i))
    (F : ∀ i, InitialFamData R (φ i))
    (S : ℝ) (hS0 : 0 ≤ S)
    (hSum : ∀ i, featureSum (fp81s21_J1 p.d) (φ i) ≤ S)
    (Kclt : ℝ) (hKclt : 0 ≤ Kclt)
    (hCLT : ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
      IsCenteredGaussianSeq G (fun j k =>
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (φ i j) (φ i k)) →
      ∀ N : ℕ, 2 ≤ N → ∀ {H : SeqL2 → ℝ}, S99.Bd 2 H →
        Integrable (fun X : EucConfig p.d N =>
          H (featureVec (φ i) (r26t3_marg R N) X)) (r26t3_Q R N) ∧
        Integrable H G ∧
        |∫ X, H (featureVec (φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N) -
          ∫ z, H z ∂G| ≤ Kclt / Real.sqrt N) :
    ∃ KL : ℝ, 0 ≤ KL ∧
      ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun j k =>
          HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (φ i j) (φ i k)) →
        ∀ N : ℕ, 2 ≤ N → ∀ {w : Euc p.d → ℝ},
          MemCb (fp81s21_k0 p.d) w → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 3 ψ →
          |(∫ X, s45_Yi N w (HRS.Whole.pair (r26t3_marg R N) w) X *
              ψ (featureVec (φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
            ∑' m, fp81s21_initial_kap (R := R) w (φ i) m *
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
  let KL : ℝ := KR * K₂ + (KT + Kclt) * p.γ⁻¹ * K₂ * S
  have hKL : 0 ≤ KL := by positivity
  refine ⟨KL, hKL, fun i {G} [IsProbabilityMeasure G] hG => ?_⟩
  have hclt := hCLT i hG
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) ((φ i) j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := (hφ i).2
  let Sb : ℝ := ∑' m, b m
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  have hSbS : Sb ≤ S := by
    simpa [featureSum, b, Sb] using hSum i
  intro N hN w hw ψ hψ
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
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec (φ i) ν X
  have hWc : Continuous W := (S99.s99_W_contDiff hN1 hJ (hφ i)).continuous
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
    p.γ⁻¹ * ⟪gradient χw x, gradient ((φ i) m) x⟫
  let Cm : ℕ → ℝ := fun m => p.γ⁻¹ * (K₂ * cw) * b m
  have hCm0 : ∀ m, 0 ≤ Cm m := fun m => by
    have := hb0 m
    positivity
  have hDφ : ∀ m x, ‖fderiv ℝ ((φ i) m) x‖ ≤ b m := fun m x =>
    s45_cb_deriv_le hJ ((hφ i).1 m) x
  have hBφ : ∀ m x, |(φ i) m x| ≤ b m := fun m x => by
    have hh := HRS.MS.Tc5.tc5_cb_sup_le ((hφ i).1 m) x
    rwa [Real.norm_eq_abs] at hh
  have hφm1 : ∀ m, ContDiff ℝ 1 ((φ i) m) := fun m =>
    ((hφ i).1 m).1.of_le (by exact_mod_cast hJ)
  have hw2bd : ∀ m x, |w2 m x| ≤ Cm m := by
    intro m x
    simp only [w2, Cm]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left
      (S99.s99_inner_grad_le hχwfeat.B1 (hDφ m) x) (inv_nonneg.2 hγ.le)).trans_eq (by ring)
  have hw2c : ∀ m, Continuous (w2 m) := fun m =>
    continuous_const.mul ((s45_contDiff_gradient hχwsmooth).continuous.inner
      (s45_gradient_continuous (hφm1 m)))
  have hcc : ∀ m, fp81s21_initial_kap (R := R) w (φ i) m =
      ∫ x, w2 m x ∂(r26t3_mu R 0) := by
    intro m
    have hφm : MemLp ((φ i) m) 2 (r26t3_mu R 0) := HRS.MS.Tc5.tc5_memLp_of_cb ((hφ i).1 m)
    have hcovResp := fp81s21_initial_cov_response_integral E hγ (hφ i) (F i) hw m
    have hcovSym := fp81s21_initial_covariance_symmetric E hγ hwl2 hφm
    have hcovW := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
      hχwfeat.smooth hχwfeat.B1 hχwfeat.B2 hwl2 hχwfeat.r2 hχwfeat.corr
      (hφm1 m) (Bφ := b m) (Dφ := b m) (hBφ m) (hDφ m)
    calc
      fp81s21_initial_kap (R := R) w (φ i) m =
          ∫ x, w x * r26t3_a R ((φ i) m) x ∂(r26t3_mu R 0) := rfl
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ ((φ i) m) w := hcovResp.symm
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ w ((φ i) m) := hcovSym.symm
      _ = p.γ⁻¹ * ∫ x, ⟪gradient χw x, gradient ((φ i) m) x⟫
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
      (fun x => ⟪gradient χw x, gradient ((φ i) m) x⟫)
  have hT2e : ∀ m X, hT2 m X = HRS.Whole.pair (HRS.Whole.empirical X) (w2 m) := by
    intro m X
    change p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χw x, gradient ((φ i) m) x⟫) =
      HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => p.γ⁻¹ * ⟪gradient χw x, gradient ((φ i) m) x⟫)
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
  have hE := fp81s21_initial_plain_response E hγ hN (hφ i) hw hχwfeat
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
              (fun x => ⟪gradient χw x, gradient ((φ i) m) x⟫)) *
            S99.pd ψ m (W X) ∂P := hE
      _ = Rlin + ∑' m, ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P := by
          rw [hfirst]
  have hdiff : ∀ m, |(∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) -
      fp81s21_initial_kap (R := R) w (φ i) m * ∫ z, S99.pd ψ m z ∂G| ≤
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
  have hκGmBd : ∀ m, ‖fp81s21_initial_kap (R := R) w (φ i) m * Gm m‖ ≤ Cm m := by
    intro m
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hcc m]
    calc
      |∫ x, w2 m x ∂(r26t3_mu R 0)| * |Gm m| ≤ Cm m * 1 :=
        mul_le_mul (hcmBd m) (hGmBd m) (abs_nonneg _) (hCm0 m)
      _ = Cm m := mul_one _
  have hsumT : Summable Tm := Summable.of_norm_bounded hCmS hTmBd
  have hsumG : Summable fun m => fp81s21_initial_kap (R := R) w (φ i) m * Gm m :=
    Summable.of_norm_bounded hCmS hκGmBd
  have hdecomp :
      (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w (φ i) m * Gm m =
        Rlin + ∑' m, (Tm m - fp81s21_initial_kap (R := R) w (φ i) m * Gm m) := by
    rw [hE', show (∑' m, ∫ X, hT2 m X * S99.pd ψ m (W X) ∂P) = ∑' m, Tm m by rfl,
      hsumT.tsum_sub hsumG]
    ring
  have hser : |∑' m, (Tm m - fp81s21_initial_kap (R := R) w (φ i) m * Gm m)| ≤
      (KT + Kclt) / Real.sqrt N * (p.γ⁻¹ * (K₂ * cw) * Sb) := by
    have hg : HasSum (fun m => (KT + Kclt) / Real.sqrt N * Cm m)
        ((KT + Kclt) / Real.sqrt N * ∑' m, Cm m) := hCmS.hasSum.mul_left _
    have hCsum : ∑' m, Cm m = p.γ⁻¹ * (K₂ * cw) * Sb := by
      simp only [Cm]
      rw [tsum_mul_left]
    rw [hCsum] at hg
    have hh := tsum_of_norm_bounded hg
      (f := fun m => Tm m - fp81s21_initial_kap (R := R) w (φ i) m * Gm m)
      (fun m => by
        rw [Real.norm_eq_abs]
        refine (hdiff m).trans (le_of_eq ?_)
        ring)
    simpa [Real.norm_eq_abs] using hh
  have hYeq :
      (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w (φ i) m * Gm m =
        (∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w (φ i) m * ∫ z, S99.pd ψ m z ∂G := by
    apply congrArg (fun z : ℝ =>
      (∫ X, Y X * ψ (W X) ∂P) - z)
    apply tsum_congr
    intro m
    simp [Gm]
  have hfinish :
      |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w (φ i) m * ∫ z, S99.pd ψ m z ∂G| ≤
        KL * cw / Real.sqrt N := by
    rw [← hYeq, hdecomp]
    calc
      |Rlin + ∑' m, (Tm m - fp81s21_initial_kap w (φ i) m * Gm m)| ≤
          |Rlin| + |∑' m, (Tm m - fp81s21_initial_kap (R := R) w (φ i) m * Gm m)| := abs_add_le _ _
      _ ≤ KR * (K₂ * cw) / Real.sqrt N +
          (KT + Kclt) / Real.sqrt N * (p.γ⁻¹ * (K₂ * cw) * Sb) := add_le_add hR hser
      _ ≤ KR * (K₂ * cw) / Real.sqrt N +
          (KT + Kclt) / Real.sqrt N * (p.γ⁻¹ * (K₂ * cw) * S) := by
        have hscale : p.γ⁻¹ * (K₂ * cw) * Sb ≤ p.γ⁻¹ * (K₂ * cw) * S :=
          mul_le_mul_of_nonneg_left hSbS (by positivity)
        have hterm : (KT + Kclt) / Real.sqrt N *
            (p.γ⁻¹ * (K₂ * cw) * Sb) ≤
            (KT + Kclt) / Real.sqrt N *
              (p.γ⁻¹ * (K₂ * cw) * S) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        exact add_le_add_right hterm _
      _ = KL * cw / Real.sqrt N := by dsimp [KL]; ring
  simpa [Y, W, P, ν, cw] using hfinish
#print axioms fp81s21_initial_Ylin_uniform_of_common_CLT

end HRS.Fp81.S21

end
