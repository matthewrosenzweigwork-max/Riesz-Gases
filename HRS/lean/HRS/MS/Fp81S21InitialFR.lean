import HRS.MS.Fp81S21InitialMab3
import HRS.MS.R2SeAux27

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
## SOL31 packet 24b: actual-law finite-rank quadratic limit

Thermal source (`S99.s99_FR`, `R2SeAux27:93`): for `h = r2FiniteRankKernel cc u`,
`Bd 4 ψ`, and a centered Gaussian sequence with susceptibility covariance at
`thermalMeasure d s a β`, there is `K ≥ 0`, chosen before `N` and `ψ`, such that

```
|Bterm d s a β γ φ N h ψ - (1 / 2) * ∑' l, ∑' q,
    Qk d s a β γ φ h l q * ∫ z, pd (pd ψ l) q z ∂G| ≤ K / sqrt N.
```

In the compiled definitions, thermal `Bterm` uses `Bh`, `S46.s46_P`,
`S46.s46_nu`, and `thermalMeasure`; thermal `Qk` uses `aRep` and the product
of two `thermalMeasure`s. Those definitions are hard-wired to the thermal law,
so this file defines the actual-law analogues with `r26t3_Q R N`,
`r26t3_marg R N`, `r26t3_mu R 0`, and `r26t3_a R`.

The already ported closure pieces are `fp81s21_initial_Mab`,
`fp81s21_initial_Mab_l`, `fp81s21_initial_E1b`,
`fp81s21_initial_Y_L2`, `fp81s21_initial_T_L2`,
`fp81s21_initial_T_L1`, `fp81s21_initial_Bq_bound`,
`fp81s21_initial_marginal_bias_s48`, `fp81s21_initial_Cf_bias_s48`,
`fp81s21_initial_mean_pairEnergy`, and `fp81s21_initial_kap`. The generic
finite-series/double-series exchange is `S99.s99_tsum2_finsum`. The remaining
finite-rank proof must combine these with the diagonal observable correction
and the centering split. It needs the actual-law Gaussian covariance shown in
the target statement; no thermal Euler equation at `R.ρ 0` is available or
used.

`r2FiniteRankKernel` is the compiled finite sum `∑ i, ∑ j, cc i j *
u i x * u j y`; `IsR2FiniteRankData` supplies symmetry, smoothness, and compact
support. The coefficient identity below is proved from these definitions and
the actual response integral, rather than treating a thermal identity as
definitional.
-/

/-- The actual-initial-law centered quadratic statistic. -/
def fp81s21_initial_Bterm {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (φ : ℕ → Euc p.d → ℝ) (N : ℕ) (h : Euc p.d → Euc p.d → ℝ)
    (ψ : SeqL2 → ℝ) : ℝ :=
  ∫ X, ((N : ℝ) * (pairEnergy h X (r26t3_mu R 0) -
      ∫ Y, pairEnergy h Y (r26t3_mu R 0) ∂(r26t3_Q R N))) *
    ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)

/-- The finite-rank response coefficient at the actual initial law. -/
def fp81s21_initial_Qk {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (φ : ℕ → Euc p.d → ℝ) (h : Euc p.d → Euc p.d → ℝ) (l q : ℕ) : ℝ :=
  ∫ z : Euc p.d × Euc p.d,
    h z.1 z.2 * r26t3_a R (φ l) z.1 * r26t3_a R (φ q) z.2
      ∂((r26t3_mu R 0).prod (r26t3_mu R 0))

/-- The actual-law `Qk` coefficient of a finite-rank kernel is the finite sum of
products of the already exported actual susceptibility coefficients. -/
theorem fp81s21_initial_Qk_finrank
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ)
    {m : ℕ} {cc : Fin m → Fin m → ℝ} {u : Fin m → Euc p.d → ℝ}
    (hcu : IsR2FiniteRankData cc u) (l q : ℕ) :
    fp81s21_initial_Qk R φ (r2FiniteRankKernel cc u) l q =
      ∑ i, ∑ j, cc i j *
        (fp81s21_initial_kap (R := R) (u i) φ l *
          fp81s21_initial_kap (R := R) (u j) φ q) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  have hu : ∀ i, Continuous (u i) := fun i => (hcu.smooth i).continuous
  have hal : Continuous (r26t3_a R (φ l)) := F.amem l |>.1.continuous
  have haq : Continuous (r26t3_a R (φ q)) := F.amem q |>.1.continuous
  let cu : Fin m → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (u i)
  have hcu0 : ∀ i, 0 ≤ cu i := fun i => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ i x, |u i x| ≤ cu i := fun i x => by
    have hu' : MemCb (fp81s21_J1 p.d) (u i) :=
      S99.s99_cb_of_cinf (hcu.smooth i) (hcu.compactSupport i) _
    have h := HRS.MS.Tc5.tc5_cb_sup_le hu' x
    simpa [cu, Real.norm_eq_abs] using h
  let bl : ℝ := cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ l))
  let bq : ℝ := cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ q))
  have hbl0 : 0 ≤ bl := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbq0 : 0 ≤ bq := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbl : ∀ x, |r26t3_a R (φ l) x| ≤ bl := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le (F.amem l) x
    simpa [bl, Real.norm_eq_abs] using h
  have hbq : ∀ x, |r26t3_a R (φ q) x| ≤ bq := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le (F.amem q) x
    simpa [bq, Real.norm_eq_abs] using h
  have hint : ∀ i j, Integrable (fun z : Euc p.d × Euc p.d =>
      cc i j * u i z.1 * u j z.2 * r26t3_a R (φ l) z.1 *
        r26t3_a R (φ q) z.2) (μ.prod μ) := by
    intro i j
    refine Integrable.of_bound
      (C := |cc i j| * cu i * cu j * bl * bq) ?_ ?_
    · exact (((((continuous_const.mul ((hu i).comp continuous_fst)).mul
        ((hu j).comp continuous_snd)).mul (hal.comp continuous_fst)).mul
        (haq.comp continuous_snd))).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul]
      calc
        abs (cc i j) * abs (u i z.1) * abs (u j z.2) *
            abs (r26t3_a R (φ l) z.1) * abs (r26t3_a R (φ q) z.2)
          ≤ abs (cc i j) * cu i * abs (u j z.2) *
            abs (r26t3_a R (φ l) z.1) * abs (r26t3_a R (φ q) z.2) := by
              gcongr
              all_goals try positivity
              all_goals exact hubd i z.1
        _ ≤ abs (cc i j) * cu i * cu j *
            abs (r26t3_a R (φ l) z.1) * abs (r26t3_a R (φ q) z.2) := by
              gcongr
              · exact mul_nonneg (abs_nonneg _) (hcu0 i)
              · exact hubd j z.2
        _ ≤ abs (cc i j) * cu i * cu j * bl *
            abs (r26t3_a R (φ q) z.2) := by
              gcongr
              · exact mul_nonneg (mul_nonneg (abs_nonneg _) (hcu0 i)) (hcu0 j)
              · exact hbl z.1
        _ ≤ abs (cc i j) * cu i * cu j * bl * bq := by
              gcongr
              · exact mul_nonneg
                  (mul_nonneg (mul_nonneg (abs_nonneg _) (hcu0 i)) (hcu0 j)) hbl0
              · exact hbq z.2
  have e1 : (fun z : Euc p.d × Euc p.d =>
      (∑ i, ∑ j, cc i j * u i z.1 * u j z.2) *
        r26t3_a R (φ l) z.1 * r26t3_a R (φ q) z.2) =
      fun z => ∑ i, ∑ j, cc i j * u i z.1 * u j z.2 *
        r26t3_a R (φ l) z.1 * r26t3_a R (φ q) z.2 := by
    funext z
    simp only [Finset.sum_mul]
  unfold fp81s21_initial_Qk r2FiniteRankKernel
  rw [e1, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 : (fun z : Euc p.d × Euc p.d =>
      cc i j * u i z.1 * u j z.2 * r26t3_a R (φ l) z.1 *
        r26t3_a R (φ q) z.2) =
      fun z => cc i j * ((u i z.1 * r26t3_a R (φ l) z.1) *
        (u j z.2 * r26t3_a R (φ q) z.2)) := by
    funext z
    ring
  rw [e2, integral_const_mul]
  congr 1
  exact integral_prod_mul (μ := μ) (ν := μ)
    (fun x => u i x * r26t3_a R (φ l) x)
    (fun y => u j y * r26t3_a R (φ q) y)

#print axioms fp81s21_initial_Qk_finrank

end HRS.Fp81.S21

end
