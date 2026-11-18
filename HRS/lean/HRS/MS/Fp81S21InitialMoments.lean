import HRS.MS.Fp81S21InitialCoord2
import HRS.MS.S21F_S06

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-!
Thermal source contracts (S99, with `μ = thermalMeasure d s a β`, `P = S46.s46_P`,
`ν = S46.s46_nu`, and `Y_u = s45_Yi N u (pair ν u)`):

* `s99_Y_L2` (`R2SeAux7:60`): for `N ≥ 2`, `B ≥ 0`, measurable `u` with
  `|u| ≤ B`, `Y_u²` is integrable and `∫Y_u² dP ≤ (K B)²`.
* `s99_T_L2` (`R2SeAux7:198`): under the same scalar test assumptions,
  `∫(pair (empirical X) u - pair μ u)² dP ≤ (K B)²/N`.
* `s99_T_L1` (`R2SeAux17:33`): from a `T_L2` constant `KT`,
  `∫|pair (empirical X)u - pair μu| dP ≤ KT B / √N`.
* `s99_Bq_bound` (`R2SeAux7:224`): for `Bq = N(pairEnergy hχ - E_P pairEnergy hχ)`,
  `hχ = commutatorKernel d s (gradient χ)`, and `‖D²χ‖ ≤ B₂`, both
  `∫Bq² dP ≤ (K B₂)²` and `∫|Bq| dP ≤ K B₂`.

Dependency classification for this port:
`Y_L2` and `T_L2` are generic variance/bias arguments; their needed static
estimates are ported by `r26t3_static_scalar` (`S21F_S06`) and exchangeability
comes from `InitialSteinEnv`. `T_L1` is generic Cauchy–Schwarz from `T_L2`.
`Bq` is a generic centered pair-energy observable, but its uniform moment/tail
input is thermal-only in S99 and is replaced by `r26t3_static_moments`
(`S21F_S07`); its commutator kernel envelope is supplied by `S21L_S08`.
Feature-index summability uses the generic `IsSummableFeatureFamily` estimates
and the actual-law covariance bounds in `S47` / `S21F_S06`.
-/

/-- Initial-law `Y_L2`: the S99 feature-linear statistic is centered at the
actual first marginal of `r26t3_Q`. -/
theorem fp81s21_initial_Y_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B →
      ∀ u : Euc p.d → ℝ, Measurable u → (∀ x, |u x| ≤ B) →
        Integrable (fun X : EucConfig p.d N =>
          (s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X) ^ 2)
          (r26t3_Q R N) ∧
        ∫ X, (s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X) ^ 2
          ∂(r26t3_Q R N) ≤ (K * B) ^ 2 := by
  obtain ⟨C, hC, hstatic⟩ := r26t3_static_scalar hδ hδh R hγ
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun N hN B hB u hu hub => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hEx : HRS.Whole.IsExchangeable (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hmean :
      ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) u ∂(r26t3_Q R N) =
        HRS.Whole.pair (r26t3_marg R N) u := by
    change ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) u ∂(r26t3_Q R N) =
      HRS.Whole.pair (HRS.Whole.firstMarginal (r26t3_Q R N)) u
    exact S45.s45_E_pair_empirical hN1 hEx hu hub
  have hvar := (hstatic N hN).1 u
  have hu2 : MemLp u 2 (r26t3_mu R 0) := by
    refine MemLp.of_bound hu.aestronglyMeasurable B ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hub x
  have hvar' := hvar hu2
  have hconstI : Integrable (fun _ : Euc p.d => B ^ 2) (r26t3_mu R 0) :=
    integrable_const (μ := r26t3_mu R 0) _
  have hIu : ∫ x, u x ^ 2 ∂(r26t3_mu R 0) ≤ B ^ 2 := by
    calc ∫ x, u x ^ 2 ∂(r26t3_mu R 0) ≤ ∫ _x, B ^ 2 ∂(r26t3_mu R 0) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x : Euc p.d => sq_nonneg (u x)) hconstI ?_
          filter_upwards with x
          exact (sq_abs (u x)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (hub x) 2)
      _ = B ^ 2 := by simp
  let g : EucConfig p.d N → ℝ := fun X => HRS.Whole.pair (HRS.Whole.empirical X) u
  let Y : EucConfig p.d N → ℝ := fun X => s45_Yi N u
    (HRS.Whole.pair (r26t3_marg R N) u) X
  have hgm : Measurable g := S45.s45_measurable_pair_empirical hN1 hu
  have hgb : ∀ X, |g X| ≤ B := fun X => S45.s45_abs_pair_empirical_le hN1 hub X
  have hgI : Integrable g (r26t3_Q R N) :=
    Integrable.of_bound hgm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hgb X)
  have hYm : Measurable Y := by
    dsimp [Y, s45_Yi]
    exact measurable_const.mul (hgm.sub measurable_const)
  have hYmean : ∫ X, Y X ∂(r26t3_Q R N) = 0 := by
    dsimp [Y, s45_Yi]
    rw [integral_const_mul, integral_sub hgI (integrable_const _), hmean]
    simp
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  have hpairν : |HRS.Whole.pair (r26t3_marg R N) u| ≤ B :=
    HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hub x)
  have hYb : ∀ X, |Y X| ≤ 2 * Real.sqrt N * B := by
    intro X
    dsimp [Y, s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt N * |g X - HRS.Whole.pair (r26t3_marg R N) u|
        ≤ Real.sqrt N * (|g X| + |HRS.Whole.pair (r26t3_marg R N) u|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (B + B) :=
          mul_le_mul_of_nonneg_left (add_le_add (hgb X) hpairν) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * B := by ring
  have hY2int : Integrable (fun X => Y X ^ 2) (r26t3_Q R N) := by
    refine Integrable.of_bound (hYm.pow_const 2).aestronglyMeasurable
      ((2 * Real.sqrt N * B) ^ 2) ?_
    filter_upwards with X
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb X) 2
  have hYvar : variance Y (r26t3_Q R N) = N * variance g (r26t3_Q R N) := by
    rw [variance_eq_integral hYm.aemeasurable, hYmean,
      variance_eq_integral hgm.aemeasurable, hmean]
    simp only [sub_zero]
    rw [← integral_const_mul]
    congr 1
    funext X
    dsimp [Y, g, s45_Yi]
    rw [mul_pow, Real.sq_sqrt hN0.le]
  have hYsecond :
      ∫ X, Y X ^ 2 ∂(r26t3_Q R N) = variance Y (r26t3_Q R N) := by
    rw [variance_eq_integral hYm.aemeasurable, hYmean]
    simp
  have hbound : ∫ X, Y X ^ 2 ∂(r26t3_Q R N) ≤ C * B ^ 2 := by
    rw [hYsecond, hYvar]
    calc (N : ℝ) * variance g (r26t3_Q R N)
        ≤ C * ∫ x, u x ^ 2 ∂(r26t3_mu R 0) := hvar'
      _ ≤ C * B ^ 2 := mul_le_mul_of_nonneg_left hIu hC
  refine ⟨hY2int, ?_⟩
  have hsqrt : (Real.sqrt C * B) ^ 2 = C * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  rw [hsqrt]
  exact hbound

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_Y_L2
