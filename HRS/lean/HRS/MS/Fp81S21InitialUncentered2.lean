import HRS.MS.Fp81S21InitialUncentered
import HRS.MS.S21F_S06

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
Thermal source contract for the coefficient term (S99):
* `S99.s99_E1_plain` (`R2SeAux9:81`, via `s99_E1`, `Aux6:34`) is the thermal uncentered
  response identity; it uses `S46.s46_stein_id` and the thermal static data.
* `S99.Cf` (`Aux14:26`) is susceptibility covariance, and `s99_cov_eq_w` (`Aux16:54`)
  identifies it with the corrector integral using thermal `s99_cov_corr` (`Aux11:178`), itself
  based on `S46.s46_cov_identity`.
* `s99_A_rate` (`Aux17:31`) isolates the deterministic coefficient bias through
  `s99_bias` (`Aux7:128`), the thermal `S46.S46Static.marg` estimate with `δ_N = 1/N`.
  The expectation of the empirical pairing is the first-marginal pairing by the generic
  exchangeability lemma `s45_E_pair_empirical` (`QsfBridge1:101`). The generic pair-energy
  decomposition is `s99_pairE_decomp` (`Aux4:26`).

For the actual initial law, `S47.s47_cov_identity` supplies the nonthermal covariance-to-corrector
identity, while `r26t3_static_scalar` (`S21F_S06:21–28`) supplies the needed actual marginal
bias. The product bound below retains `cbNorm (fp81s21_J1 p.d)` on each input. The derivative
weighted form is the deterministic bias times an expected bounded second derivative, as in the
`β0 * ∫ ψ` term of `s99_A_rate`; no `S48.s48_Q` hypothesis is needed for this coefficient clause.
The iid/log preparation's zero-bias branch and the `γ = 0` corner are outside this positive-γ
port. `r26t3_actual_density` is not needed here: all coefficient observables are bounded and the
static scalar theorem applies directly.
-/

/-- The actual initial-law analogue of the S99 coefficient `Cf`. -/
def fp81s21_initial_Cf {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (_F : InitialFamData R φ) (j l : ℕ) : ℝ :=
  HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ (φ j) (φ l)

/-- At the actual initial law, the susceptibility coefficient is the integral of the compatible
response-gradient observable `wF`. -/
theorem fp81s21_initial_Cf_eq_wF
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (j l : ℕ) :
    fp81s21_initial_Cf F j l =
      ∫ x, InitialFamData.wF F j l x ∂(r26t3_mu R 0) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hd2 : (p.d : ℝ) / 2 ≤ (p.d : ℝ) := by nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hJ : 1 ≤ fp81s21_J1 p.d := by
    unfold fp81s21_J1
    omega
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hfeat := F.feat hγ j
  have hφj : MemLp (φ j) 2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 j)
  have hφl1 : ContDiff ℝ 1 (φ l) := (hφ.1 l).1.of_le (by exact_mod_cast hJ)
  have hBφ : ∀ x, |φ l x| ≤ cbNorm (fp81s21_J1 p.d) (φ l) := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 l) x
    rwa [Real.norm_eq_abs] at h
  have hDφ : ∀ x, ‖fderiv ℝ (φ l) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ l) := by
    intro x
    exact s45_cb_deriv_le (by exact_mod_cast hJ) (hφ.1 l) x
  have hcov := S47.s47_cov_identity p.hd p.hs0 hsd hγ E.reference
    hfeat.smooth hfeat.B1 hfeat.B2 hφj hfeat.r2 hfeat.corr hφl1
    (Bφ := cbNorm (fp81s21_J1 p.d) (φ l))
    (Dφ := cbNorm (fp81s21_J1 p.d) (φ l)) hBφ hDφ
  change HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
    (φ j) (φ l) = _
  calc
    _ = p.γ⁻¹ * ∫ x, ⟪gradient (F.χ j) x, gradient (φ l) x⟫ ∂(r26t3_mu R 0) := hcov
    _ = ∫ x, p.γ⁻¹ * ⟪gradient (F.χ j) x, gradient (φ l) x⟫ ∂(r26t3_mu R 0) := by
      rw [integral_const_mul]
    _ = _ := by rfl

/-- The actual-law coefficient bias is order `N⁻¹`, with the original feature norms on both
inputs. The mean of the empirical coefficient is expressed at the actual first marginal. -/
theorem fp81s21_initial_Cf_bias
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ j l : ℕ,
      |(∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
          ∂(r26t3_Q R N)) - fp81s21_initial_Cf F j l| ≤
        C * (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
          cbNorm (fp81s21_J1 p.d) (φ l)) / (N : ℝ) := by
  obtain ⟨C, hC, hstatic⟩ := r26t3_static_scalar hδ hδh R hγ
  refine ⟨C, hC, fun N hN j l => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hB : 0 ≤ p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
      cbNorm (fp81s21_J1 p.d) (φ l) := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le)
      (mul_nonneg F.hK (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
      (HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hwbd : ∀ x, |InitialFamData.wF F j l x| ≤
      p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
        cbNorm (fp81s21_J1 p.d) (φ l) := by
    intro x
    unfold InitialFamData.wF
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    have hinner := abs_real_inner_le_norm (gradient (F.χ j) x) (gradient (φ l) x)
    have hχ0 := F.deriv j x 0 (Nat.zero_le _)
    have hχgrad : ‖gradient (F.χ j) x‖ ≤
        F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
      rw [s45_norm_gradient, ← norm_iteratedFDeriv_one]
      exact hχ0
    have hφ0 := s45_cb_deriv_le (by exact_mod_cast (show
      1 ≤ fp81s21_J1 p.d by unfold fp81s21_J1; omega)) (hφ.1 l) x
    have hφgrad : ‖gradient (φ l) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ l) := by
      rw [s45_norm_gradient]
      exact hφ0
    calc
      p.γ⁻¹ * |⟪gradient (F.χ j) x, gradient (φ l) x⟫| ≤
          p.γ⁻¹ * (‖gradient (F.χ j) x‖ * ‖gradient (φ l) x‖) :=
        mul_le_mul_of_nonneg_left hinner (inv_nonneg.2 hγ.le)
      _ ≤ p.γ⁻¹ * ((F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
          cbNorm (fp81s21_J1 p.d) (φ l)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hχgrad hφgrad (norm_nonneg _) (by
            exact mul_nonneg F.hK (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
          (inv_nonneg.2 hγ.le)
      _ = _ := by ring
  have hwmeas : Measurable (InitialFamData.wF F j l) := by
    have hW := fp81s21_initial_wF_cb hφ.1 F hγ j l
    exact hW.1.1.continuous.measurable
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hEx : HRS.Whole.IsExchangeable (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hEmp :
      ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
        ∂(r26t3_Q R N) =
      HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j l) :=
    s45_E_pair_empirical hN1 hEx hwmeas hwbd
  have hCf := fp81s21_initial_Cf_eq_wF E hγ hφ F j l
  have hCfPair : fp81s21_initial_Cf F j l =
      HRS.Whole.pair (r26t3_mu R 0) (InitialFamData.wF F j l) := by
    rw [hCf]
    rfl
  rw [hEmp, hCfPair]
  rcases hstatic N hN with ⟨_, hmarg⟩
  exact hmarg (InitialFamData.wF F j l) hwmeas _ hwbd

/-- Derivative-weighted form of the deterministic coefficient bias. For the S99 use, take
`a = ∫ X, pd (pd f j) l (featureVec φ (r26t3_marg R N) X) ∂Q`; the bounded derivative factor
is then supplied by `SteinCl`, without a shifted `S48.s48_Q` norm. -/
theorem fp81s21_initial_Cf_bias_mul
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ j l : ℕ,
      ∀ a D : ℝ, 0 ≤ D → |a| ≤ D →
      |((∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
          ∂(r26t3_Q R N)) - fp81s21_initial_Cf F j l) * a| ≤
        C * (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
          cbNorm (fp81s21_J1 p.d) (φ l)) / (N : ℝ) * D := by
  obtain ⟨C, hC, hbias⟩ := fp81s21_initial_Cf_bias hδ hδh E hγ hφ F
  refine ⟨C, hC, fun N hN j l a D hD ha => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hInput : 0 ≤ p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
      cbNorm (fp81s21_J1 p.d) (φ l) := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le)
      (mul_nonneg F.hK (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
      (HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hB0 : 0 ≤ C * (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
      cbNorm (fp81s21_J1 p.d) (φ l)) / (N : ℝ) :=
    div_nonneg (mul_nonneg hC hInput) (Nat.cast_nonneg N)
  calc
    |((∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
        ∂(r26t3_Q R N)) - fp81s21_initial_Cf F j l) * a| =
        |(∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l)
          ∂(r26t3_Q R N)) - fp81s21_initial_Cf F j l| * |a| := abs_mul _ _
    _ ≤ (C * (p.γ⁻¹ * (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
          cbNorm (fp81s21_J1 p.d) (φ l)) / (N : ℝ)) * D :=
        mul_le_mul (hbias N hN j l) ha (abs_nonneg _) hB0
    _ = _ := by ring

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_Cf_eq_wF
#print axioms HRS.Fp81.S21.fp81s21_initial_Cf_bias
#print axioms HRS.Fp81.S21.fp81s21_initial_Cf_bias_mul
