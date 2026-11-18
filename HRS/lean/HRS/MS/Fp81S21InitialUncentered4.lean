import HRS.MS.Fp81S21InitialUncentered3
import HRS.MS.DerCorAux1
import HRS.MS.SA16Y3L2a

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
The thermal source is `S99.s99_A_rate` (`R2SeAux18:31`), whose deterministic coefficient
term is estimated through `S99.s99_bias` (`R2SeAux7:128`). That thermal bias only uses the
full supremum bound. The actual-law `InitialSteinEnv.static.marg` contains the stronger
`S47Static` density-ratio estimate in `L²(μ)`. Pairing it with the centered observable in
`L²(μ)` gives the derivative-sensitive `s48_Q` bound below.
-/

/-- Derivative-sensitive actual-marginal bias for any bounded smooth observable. The centered
`L²` factor is controlled by `S48.s48_Q`, which includes only the centered value and positive
derivative seminorms. -/
theorem fp81s21_initial_marginal_bias_s48
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {N : ℕ} (hN : 2 ≤ N)
    {J : ℕ} {f : Euc p.d → ℝ} (hf : MemCb J f) :
    |HRS.Whole.pair (r26t3_marg R N) f - HRS.Whole.pair (r26t3_mu R 0) f| ≤
      E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J f / (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hS := E.static N hN
  have hνeq0 : S47.s47_nu p.d p.s (R.ρ 0) p.γ N = r26t3_marg R N := by
    change HRS.Whole.firstMarginal (S47.s47_P p.d p.s (R.ρ 0) p.γ N) =
      HRS.Whole.firstMarginal (r26t3_Q R N)
    rw [E.law_eq N]
  haveI hμdens : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  obtain ⟨r, hrm, hrν, hrc, hr2, hrn⟩ := hS.marg
  have hν : S47.s47_nu p.d p.s (R.ρ 0) p.γ N =
      (r26t3_mu R 0).withDensity (fun x => ENNReal.ofReal (r x)) := hrν
  have hνprob : IsProbabilityMeasure (S47.s47_nu p.d p.s (R.ρ 0) p.γ N) :=
    S47.s47_nu_prob hN hS.prob
  have hr0 : ∀ x, 0 ≤ r x := fun x => (hrc x).1
  have hB : 0 ≤ cbNorm J f := HRS.MS.Tc5.tc5_cb_nonneg J f
  have hfb : ∀ x, |f x| ≤ cbNorm J f := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le hf x
    rwa [Real.norm_eq_abs] at h
  have hfm : Measurable f := hf.1.continuous.measurable
  have hf2 : MemLp f 2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb hf
  have hpair : |HRS.Whole.pair (r26t3_mu R 0) f| ≤ cbNorm J f :=
    HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hfb x)
  have hcenterBound : ∀ x, |HRS.Whole.projMean (r26t3_mu R 0) f x| ≤
      2 * cbNorm J f := by
    intro x
    unfold HRS.Whole.projMean
    calc |f x - HRS.Whole.pair (r26t3_mu R 0) f| ≤
        |f x| + |HRS.Whole.pair (r26t3_mu R 0) f| := abs_sub _ _
      _ ≤ 2 * cbNorm J f := by linarith [hfb x, hpair]
  have hcenterLp : MemLp (HRS.Whole.projMean (r26t3_mu R 0) f)
      2 (r26t3_mu R 0) := by
    refine MemLp.of_bound ?_ (2 * cbNorm J f) ?_
    · exact (hf.1.continuous.sub continuous_const).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hcenterBound x
  have hfi : Integrable f (r26t3_mu R 0) := hf2.integrable one_le_two
  have hrf : Integrable (fun x => r x * f x) (r26t3_mu R 0) := by
    refine Integrable.of_bound ((hrm.mul hfm).aestronglyMeasurable)
      (E.Cs * cbNorm J f) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 x)]
    exact mul_le_mul (hrc x).2 (hfb x) (abs_nonneg _)
      E.Cs_nonneg
  have hνf : HRS.Whole.pair (S47.s47_nu p.d p.s (R.ρ 0) p.γ N) f =
      ∫ x, r x * f x ∂(r26t3_mu R 0) := by
    unfold HRS.Whole.pair
    rw [hν, integral_withDensity_eq_integral_toReal_smul hrm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hr0 _)]
  have hνone : ∫ x, (1 : ℝ) ∂(S47.s47_nu p.d p.s (R.ρ 0) p.γ N) = 1 := by
    simp
  rw [hν] at hνone
  rw [integral_withDensity_eq_integral_toReal_smul hrm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hνone
  have hrInt : ∫ x, r x ∂(r26t3_mu R 0) = 1 := by
    simpa only [smul_eq_mul, ENNReal.toReal_ofReal (hr0 _), mul_one] using hνone
  have hmean : ∫ x, (r x - 1) ∂(r26t3_mu R 0) = 0 := by
    have hrI : Integrable r (r26t3_mu R 0) := by
      refine Integrable.of_bound hrm.aestronglyMeasurable E.Cs ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 x)]
      exact (hrc x).2
    rw [integral_sub hrI (integrable_const 1), hrInt]
    simp
  have hdiff :
      HRS.Whole.pair (S47.s47_nu p.d p.s (R.ρ 0) p.γ N) f -
        HRS.Whole.pair (r26t3_mu R 0) f =
      ∫ x, (r x - 1) * f x ∂(r26t3_mu R 0) := by
    rw [hνf]
    unfold HRS.Whole.pair
    rw [← integral_sub hrf hfi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hgLp : MemLp (fun x => r x - 1) 2 (r26t3_mu R 0) := by
    simpa [r26t3_mu] using hr2
  have hprodI : Integrable
      (fun x => (r x - 1) * HRS.Whole.projMean (r26t3_mu R 0) f x)
      (r26t3_mu R 0) := hgLp.integrable_mul hcenterLp
  have hconstI : Integrable (fun x => (r x - 1) * HRS.Whole.pair (r26t3_mu R 0) f)
      (r26t3_mu R 0) := hr2.integrable one_le_two |>.mul_const _
  have hconst : ∫ x, (r x - 1) * HRS.Whole.pair (r26t3_mu R 0) f
      ∂(r26t3_mu R 0) = 0 := by
    calc
      _ = HRS.Whole.pair (r26t3_mu R 0) f * ∫ x, (r x - 1) ∂(r26t3_mu R 0) := by
        rw [show (fun x => (r x - 1) * HRS.Whole.pair (r26t3_mu R 0) f) =
          fun x => HRS.Whole.pair (r26t3_mu R 0) f * (r x - 1) from funext fun x => by ring,
          integral_const_mul]
      _ = 0 := by rw [hmean]; ring
  have hcenter : ∫ x, (r x - 1) * f x ∂(r26t3_mu R 0) =
      ∫ x, (r x - 1) * HRS.Whole.projMean (r26t3_mu R 0) f x
        ∂(r26t3_mu R 0) := by
    have heq : (fun x => (r x - 1) * f x) = fun x =>
        (r x - 1) * HRS.Whole.projMean (r26t3_mu R 0) f x +
          (r x - 1) * HRS.Whole.pair (r26t3_mu R 0) f := by
      funext x
      unfold HRS.Whole.projMean
      ring
    rw [heq, integral_add hprodI hconstI, hconst]
    simp
  have hcenterLp' : MemLp (HRS.Whole.projMean (r26t3_mu R 0) f)
      (ENNReal.ofReal 2) (r26t3_mu R 0) := by
    simpa using hcenterLp
  have hgLp' : MemLp (fun x => r x - 1) (ENNReal.ofReal 2)
      (r26t3_mu R 0) := by
    simpa using hgLp
  have hcs := HRS.Whole.AppendixA.Phase2SA16R.sa16y3_cs hcenterLp' hgLp'
  have hNcenter : HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2
      (HRS.Whole.projMean (r26t3_mu R 0) f) (r26t3_mu R 0) =
      HRS.Whole.l2Norm (r26t3_mu R 0) (HRS.Whole.projMean (r26t3_mu R 0) f) := by
    rw [HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2_eq hcenterLp']
    simp [HRS.Whole.l2Norm, Real.sqrt_eq_rpow, Real.norm_eq_abs]
  have hNratio : HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2
      (fun x => r x - 1) (r26t3_mu R 0) =
      HRS.Whole.l2Norm (r26t3_mu R 0) (fun x => r x - 1) := by
    rw [HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2_eq hgLp']
    simp [HRS.Whole.l2Norm, Real.sqrt_eq_rpow, Real.norm_eq_abs]
  have hδN : HRS.deltaN p.d p.s N = (N : ℝ)⁻¹ := by
    rw [HRS.Whole.deltaN_eq]
    simp [p.hs]
  have hrBound : HRS.Whole.l2Norm (r26t3_mu R 0) (fun x => r x - 1) ≤
      E.Cs / (N : ℝ) := by
    change HRS.Whole.l2Norm (HRS.Whole.withDensityReal (R.ρ 0))
      (fun x => r x - 1) ≤ E.Cs / (N : ℝ)
    calc
      _ ≤ E.Cs * HRS.deltaN p.d p.s N := hrn
      _ = E.Cs / (N : ℝ) := by rw [hδN]; ring
  have hQ0 : 0 ≤ HRS.MS.S48.s48_Q (r26t3_mu R 0) J f :=
    HRS.MS.S48.s48_Q_nonneg (r26t3_mu R 0) J f
  have hQbound : HRS.Whole.l2Norm (r26t3_mu R 0)
      (HRS.Whole.projMean (r26t3_mu R 0) f) ≤
        HRS.MS.S48.s48_Q (r26t3_mu R 0) J f := HRS.MS.S48.s48_l2_le_Q _ _ _
  rw [← hνeq0]
  rw [hdiff, hcenter]
  have hcsSwap :
      |∫ x, (r x - 1) * HRS.Whole.projMean (r26t3_mu R 0) f x
          ∂(r26t3_mu R 0)| =
        |∫ x, HRS.Whole.projMean (r26t3_mu R 0) f x * (r x - 1)
          ∂(r26t3_mu R 0)| := by
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  calc
    |∫ x, (r x - 1) * HRS.Whole.projMean (r26t3_mu R 0) f x
        ∂(r26t3_mu R 0)| ≤
      HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2
          (HRS.Whole.projMean (r26t3_mu R 0) f) (r26t3_mu R 0) *
        HRS.Whole.AppendixA.Phase2SA16R.sa16y3_N2
          (fun x => r x - 1) (r26t3_mu R 0) := by rw [hcsSwap]; exact hcs
    _ ≤ HRS.MS.S48.s48_Q (r26t3_mu R 0) J f * (E.Cs / (N : ℝ)) := by
      rw [hNcenter, hNratio]
      exact mul_le_mul hQbound hrBound (Real.sqrt_nonneg _) hQ0
    _ = E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J f / (N : ℝ) := by ring

/-- The derivative-sensitive deterministic coefficient estimate for `wF`. -/
theorem fp81s21_initial_Cf_bias_s48
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    ∀ N : ℕ, 2 ≤ N → ∀ j l : ℕ,
      |(∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
          ∂(r26t3_Q R N)) - fp81s21_initial_Cf F j l| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) (fp81s21_k0 p.d)
          (InitialFamData.wF F j l) / (N : ℝ) := by
  intro N hN j l
  have hN1 : 1 ≤ N := by omega
  have hwcb := fp81s21_initial_wF_cb hφ.1 F hγ j l
  have hf : MemCb (fp81s21_k0 p.d) (InitialFamData.wF F j l) := hwcb.1
  have hfb : ∀ x, |InitialFamData.wF F j l x| ≤
      cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j l) := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le hf x
    rwa [Real.norm_eq_abs] at h
  have hfm : Measurable (InitialFamData.wF F j l) :=
    hf.1.continuous.measurable
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hEx : HRS.Whole.IsExchangeable (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hEmp :
      ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l) ∂(r26t3_Q R N) =
        HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j l) :=
    s45_E_pair_empirical hN1 hEx hfm hfb
  have hBias := fp81s21_initial_marginal_bias_s48 E hN hf
  have hCf := fp81s21_initial_Cf_eq_wF E hγ hφ F j l
  rw [hEmp, hCf]
  exact hBias

#print axioms fp81s21_initial_marginal_bias_s48
#print axioms fp81s21_initial_Cf_bias_s48
end HRS.Fp81.S21

end
