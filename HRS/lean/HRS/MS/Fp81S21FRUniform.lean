import HRS.MS.Fp81S21InitialMab2
import HRS.MS.Fp81S21UnifLinSeries4

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

/-- A single per-feature mixed quadratic rate for a feature family with a common sum bound. -/
theorem fp81s21_initial_Mab_l_uniform
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {ι : Type} (Φ : ι → ℕ → Euc p.d → ℝ)
    (hΦ : ∀ i, IsSummableFeatureFamily (fp81s21_J1 p.d) (Φ i))
    (F : ∀ i, InitialFamData R (Φ i))
    (S : ℝ) (hS0 : 0 ≤ S)
    (hSum : ∀ i, featureSum (fp81s21_J1 p.d) (Φ i) ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
      IsCenteredGaussianSeq G (fun j k =>
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (Φ i j) (Φ i k)) →
      ∀ N : ℕ, 2 ≤ N → ∀ {u v : Euc p.d → ℝ},
      MemCb (fp81s21_J1 p.d) u → MemCb (fp81s21_J1 p.d) v →
      ∀ {χ : Euc p.d → ℝ} {Bχ : ℝ},
        S47.S47Feat p.d p.s (R.ρ 0) p.γ u χ Bχ →
      ∀ {ψ : SeqL2 → ℝ}, S99.Bd 4 ψ → ∀ l : ℕ,
      |(∫ X, (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient ((Φ i) l) x⟫)) *
          (s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X *
            S99.pd ψ l (featureVec (Φ i) (r26t3_marg R N) X)) ∂(r26t3_Q R N)) -
        fp81s21_initial_kap (R := R) u (Φ i) l *
          ∑' q, fp81s21_initial_kap (R := R) v (Φ i) q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤
        K * Bχ * cbNorm (fp81s21_J1 p.d) v *
          cbNorm (fp81s21_J1 p.d) ((Φ i) l) / Real.sqrt N := by
  obtain ⟨KT, hKT0, hTL2⟩ := fp81s21_initial_T_L2 hδ hδh E hγ
  obtain ⟨KY, hKY0, hY2⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  obtain ⟨Kclt, hKclt0, hCLT⟩ :=
    fp81s21_initial_clt_uniform_of_featureSum_bound hδh R hγ Φ hΦ S hS0 hSum
  obtain ⟨KL, hKL0, hYlin⟩ :=
    fp81s21_initial_Ylin_uniform_of_common_CLT hδ hδh R E hγ Φ hΦ F S hS0 hSum
      Kclt hKclt0 hCLT
  refine ⟨p.γ⁻¹ * (KT * KY + KL), by positivity, ?_⟩
  intro i G _ hG N hN u v hu hv χ Bχ hχ ψ hψ l
  let φ := Φ i
  have hφ := hΦ i
  have F := F i
  have hYlin := hYlin i hG
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hk0 : 1 ≤ fp81s21_k0 p.d := fp81s21_k0_ge_one p.d
  have hJ1 : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hk0J : fp81s21_k0 p.d ≤ fp81s21_J1 p.d := by
    have h := fp81s21_J1_ge_k0 p.d
    omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := s99_nu_prob hN1
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  haveI hμdens : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hu0 : MemCb (fp81s21_k0 p.d) u :=
    (HRS.MS.Tc5.tc5_cb_mono hk0J hu).1
  have huLp : MemLp u 2 (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.Tc5.tc5_memLp_of_cb hu0
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hχ.B1 0)
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  let cv : ℝ := cbNorm (fp81s21_J1 p.d) v
  have hcv0 : 0 ≤ cv := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hvbd : ∀ x, |v x| ≤ cv := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hv x
    simpa [cv, Real.norm_eq_abs] using h
  have hvc1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast hJ1)
  have hvm : Measurable v := hvc1.continuous.measurable
  have hv0 : MemCb (fp81s21_k0 p.d) v :=
    (HRS.MS.Tc5.tc5_cb_mono hk0J hv).1
  have hcvk : cbNorm (fp81s21_k0 p.d) v ≤ cv :=
    (HRS.MS.Tc5.tc5_cb_mono hk0J hv).2
  have hφl1 : ContDiff ℝ 1 (φ l) := (hφ.1 l).1.of_le (by exact_mod_cast hJ1)
  have hDφ : ∀ x, ‖fderiv ℝ (φ l) x‖ ≤ b l := fun x =>
    s45_cb_deriv_le hJ1 (hφ.1 l) x
  have hφlLp : MemLp (φ l) 2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 l)
  have hχgrad : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ.smooth
  let w2 : Euc p.d → ℝ := fun x =>
    p.γ⁻¹ * ⟪gradient χ x, gradient (φ l) x⟫
  let Cl : ℝ := p.γ⁻¹ * Bχ * b l
  have hCl0 : 0 ≤ Cl := by
    dsimp [Cl]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le) hBχ0) (hb0 l)
  have hw2bd : ∀ x, |w2 x| ≤ Cl := by
    intro x
    dsimp [w2, Cl]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left
      (s99_inner_grad_le hχ.B1 hDφ x) (inv_nonneg.2 hγ.le)).trans_eq (by ring)
  have hw2c : Continuous w2 :=
    continuous_const.mul (hχgrad.continuous.inner (s45_gradient_continuous hφl1))
  have hw2m : Measurable w2 := hw2c.measurable
  have hCov :
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0)
        p.γ u (φ l) = ∫ x, w2 x ∂(r26t3_mu R 0) := by
    have hsd : p.s < (p.d : ℝ) := by
      have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
      linarith [p.hs]
    have hcov := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
      hχ.smooth hχ.B1 hχ.B2 huLp
      hχ.r2 hχ.corr hφl1
      (Bφ := b l) (Dφ := b l)
      (fun x => by
        have h := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 l) x
        simpa [b, Real.norm_eq_abs] using h)
      hDφ
    have hcov' :
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (HRS.Whole.withDensityReal (R.ρ 0)) p.γ u (φ l) =
          p.γ⁻¹ * ∫ x, ⟪gradient χ x, gradient (φ l) x⟫
            ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by
      simpa [r26t3_mu] using hcov
    calc
      _ = p.γ⁻¹ * ∫ x, ⟪gradient χ x, gradient (φ l) x⟫
          ∂(HRS.Whole.withDensityReal (R.ρ 0)) := hcov'
      _ = ∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient (φ l) x⟫
          ∂(HRS.Whole.withDensityReal (R.ρ 0)) := by rw [integral_const_mul]
      _ = _ := by rfl
  have hCovSym := fp81s21_initial_covariance_symmetric E hγ
    (HRS.MS.Tc5.tc5_memLp_of_cb hu0) hφlLp
  have hKapId : fp81s21_initial_kap (R := R) u φ l =
      ∫ x, w2 x ∂(r26t3_mu R 0) := by
    change ∫ x, u x * r26t3_a R (φ l) x ∂(r26t3_mu R 0) = _
    calc
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (φ l) u :=
        (fp81s21_initial_cov_response_integral E hγ hφ F hu0 l).symm
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ u (φ l) := hCovSym.symm
      _ = _ := hCov
  let κl : ℝ := fp81s21_initial_kap (R := R) u φ l
  have hκb : |κl| ≤ Cl := by
    have hi := norm_integral_le_of_norm_le_const
      (μ := r26t3_mu R 0) (f := w2) (C := Cl)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hw2bd x)
    rw [← hKapId] at hi
    simpa [κl, Real.norm_eq_abs] using hi
  have hpw : HRS.Whole.pair (r26t3_mu R 0) w2 = κl := by
    change ∫ x, w2 x ∂(r26t3_mu R 0) = κl
    rw [← hKapId]
  have hTe : ∀ X : EucConfig p.d N,
      p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient (φ l) x⟫) =
      HRS.Whole.pair (HRS.Whole.empirical X) w2 := fun X =>
        (s99_pair_smul hN1 p.γ⁻¹ _ X).symm
  dsimp only [φ] at hTe
  simp_rw [hTe]
  have hTm : Measurable fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) w2 :=
    s45_measurable_pair_empirical hN1 hw2m
  have hTbd : ∀ X : EucConfig p.d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) w2| ≤ Cl := fun X =>
    s45_abs_pair_empirical_le hN1 hw2bd X
  let Yv : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X
  have hYvm : Measurable Yv :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hvm).sub measurable_const)
  have hYvb : ∀ X, |Yv X| ≤ 2 * Real.sqrt N * cv :=
    fun X => s99_Yi_bd hN1 hvbd X
  have hψl : S99.Bd 3 (S99.pd ψ l) := hψ.pd l
  have hWc : Continuous (fun X : EucConfig p.d N =>
      featureVec φ (r26t3_marg R N) X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψm : Measurable fun X : EucConfig p.d N =>
      S99.pd ψ l (featureVec φ (r26t3_marg R N) X) :=
    (hψl.1.continuous.comp hWc).measurable
  have hψb : ∀ X : EucConfig p.d N,
      |S99.pd ψ l (featureVec φ (r26t3_marg R N) X)| ≤ 1 :=
    fun X => hψl.abs_le _
  have hI2 : Integrable (fun X : EucConfig p.d N =>
      Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X)) (r26t3_Q R N) :=
    Integrable.of_bound (hYvm.mul hψm).aestronglyMeasurable
      (2 * Real.sqrt N * cv) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |Yv X| * |S99.pd ψ l (featureVec φ (r26t3_marg R N) X)|
            ≤ (2 * Real.sqrt N * cv) * 1 :=
              mul_le_mul (hYvb X) (hψb X) (abs_nonneg _) (by positivity)
          _ = _ := mul_one _)
  have hI1 : Integrable (fun X : EucConfig p.d N =>
      (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) *
        (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X))) (r26t3_Q R N) :=
    Integrable.of_bound ((hTm.sub measurable_const).mul (hYvm.mul hψm)).aestronglyMeasurable
      ((Cl + |κl|) * (2 * Real.sqrt N * cv))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact (abs_sub _ _).trans (add_le_add (hTbd X) le_rfl)
        · calc |Yv X| * |S99.pd ψ l (featureVec φ (r26t3_marg R N) X)|
              ≤ (2 * Real.sqrt N * cv) * 1 :=
                mul_le_mul (hYvb X) (hψb X) (abs_nonneg _) (by positivity)
            _ = _ := mul_one _)
  have hdec :
      (∫ X, HRS.Whole.pair (HRS.Whole.empirical X) w2 *
        (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) =
      (∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) *
        (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) +
        κl * ∫ X, Yv X * S99.pd ψ l
          (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul κl)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only
    ring
  have hf2 : MemLp (fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) 2 (r26t3_Q R N) :=
    s99_memLp_two_of_bdd (C := Cl + |κl|) (hTm.sub measurable_const) (fun X =>
      (abs_sub _ _).trans (add_le_add (hTbd X) le_rfl))
  have hg2 : MemLp Yv 2 (r26t3_Q R N) := s99_memLp_two_of_bdd hYvm hYvb
  have hA : ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) ^ 2
      ∂(r26t3_Q R N) ≤ (KT * Cl / Real.sqrt N) ^ 2 := by
    have h := hTL2 N hN Cl hCl0 w2 hw2m hw2bd
    rw [hpw] at h
    exact h.2.trans (le_of_eq (by rw [div_pow, Real.sq_sqrt hN0.le, mul_pow]))
  have hB : ∫ X, (Yv X) ^ 2 ∂(r26t3_Q R N) ≤ (KY * cv) ^ 2 :=
    (hY2 N hN cv hcv0 v hvm hvbd).2
  have e1 : |∫ X,
      (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) *
        (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X))
        ∂(r26t3_Q R N)| ≤ KT * Cl / Real.sqrt N * (KY * cv) := by
    have hA0 : 0 ≤ KT * Cl / Real.sqrt N := div_nonneg (mul_nonneg hKT0 hCl0) hsqN.le
    have hB0 : 0 ≤ KY * cv := mul_nonneg hKY0 hcv0
    have hcs := s99_cs_bd hf2 hg2 hA hB hA0 hB0
    refine le_trans ?_ hcs
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) ?_
      (Filter.Eventually.of_forall fun X => ?_)
    · have hfa : MemLp (fun X : EucConfig p.d N =>
          |HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl|) 2 (r26t3_Q R N) := hf2.abs
      have hga : MemLp (fun X : EucConfig p.d N => |Yv X|) 2 (r26t3_Q R N) := hg2.abs
      exact hfa.integrable_mul hga
    · beta_reduce
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl| *
            (|Yv X| * |S99.pd ψ l (featureVec φ (r26t3_marg R N) X)|)
          ≤ |HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl| * (|Yv X| * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hψb X) (abs_nonneg _)) (abs_nonneg _)
        _ = |HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl| * |Yv X| := by rw [mul_one]
  have hYl := hYlin N hN hv0 hψl
  have e2 : |κl * ((∫ X, Yv X * S99.pd ψ l
        (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
      ∑' q, fp81s21_initial_kap (R := R) v φ q *
        ∫ z, S99.pd (S99.pd ψ l) q z ∂G)| ≤
      Cl * (KL * cbNorm (fp81s21_k0 p.d) v / Real.sqrt N) := by
    rw [abs_mul]
    exact mul_le_mul hκb hYl (abs_nonneg _) hCl0
  rw [hdec]
  have e3 :
      ((∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) *
          (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) +
        κl * ∫ X, Yv X * S99.pd ψ l
          (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
        κl * ∑' q, fp81s21_initial_kap (R := R) v φ q *
          ∫ z, S99.pd (S99.pd ψ l) q z ∂G =
      (∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) w2 - κl) *
          (Yv X * S99.pd ψ l (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) +
        κl * ((∫ X, Yv X * S99.pd ψ l
            (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
          ∑' q, fp81s21_initial_kap (R := R) v φ q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G) := by ring
  rw [e3]
  refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have hKL' : KL * cbNorm (fp81s21_k0 p.d) v ≤ KL * cv :=
    mul_le_mul_of_nonneg_left hcvk hKL0
  have hfin :
      KT * Cl / Real.sqrt N * (KY * cv) +
        Cl * (KL * cbNorm (fp81s21_k0 p.d) v / Real.sqrt N) ≤
      p.γ⁻¹ * (KT * KY + KL) * Bχ * cv * b l / Real.sqrt N := by
    have heq :
        KT * Cl / Real.sqrt N * (KY * cv) +
          Cl * (KL * cbNorm (fp81s21_k0 p.d) v / Real.sqrt N) =
        (Cl * (KT * KY * cv + KL * cbNorm (fp81s21_k0 p.d) v)) / Real.sqrt N := by ring
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ hsqN.le
    have hmul : Cl * (KT * KY * cv + KL * cbNorm (fp81s21_k0 p.d) v) ≤
        Cl * ((KT * KY + KL) * cv) :=
      mul_le_mul_of_nonneg_left (by linarith [hKL']) hCl0
    exact hmul.trans (le_of_eq (by dsimp [Cl, b, cv]; ring))
  simpa [κl, Yv, w2, b, cv] using hfin

#print axioms fp81s21_initial_Mab_l_uniform

end HRS.Fp81.S21
end
