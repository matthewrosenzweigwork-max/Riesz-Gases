import HRS.MS.S82RA4

/-!
# S8.2 R01A (S82R), part 5: the reference marginal (relative `L^2`, small `N`, relative `L^infty`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wr HRS.MS.Psd

variable {d : ℕ}

namespace S82RCtx

variable {a beta : ℝ} {rho : Euc d → ℝ} {M tau CR : ℝ} {N0 : ℕ}

theorem refMarg_eq (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN1 : 0 < N) :
    refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
        (HRS.Whole.withDensityReal rho) beta N =
      HRS.Whole.firstMarginal (unpinnedReference (qTau d (criticalS d) tau)
        (s82r_field d rho beta tau N0) (HRS.Whole.withDensityReal rho) beta N) := by
  unfold refMarginal HRS.Whole.firstMarginal
  rw [dif_pos hN1, dif_pos hN1]

theorem refMarg_large (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) :
    refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
        (HRS.Whole.withDensityReal rho) beta N =
      HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y))
        (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) beta N) := by
  have hN1 : 0 < N := by have := c.hN0; omega
  rw [c.refMarg_eq hN1, c.unpinned_large hN]

theorem relL2_large (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) :
    eLpNorm (fun x => ((refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
      (HRS.Whole.withDensityReal rho) beta N).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal - 1) 2
      (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal (CR * HRS.MS.Phase2S82.deltaN N) := by
  rw [c.refMarg_large hN, ← s82r_deltaN_eq d N]
  exact (c.hL2 N hN).2

/-- Small `N`: the marginal of the zero-field reference has bounded density. -/
theorem refMarg_small_le (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN1 : 0 < N) (hN : N < N0) :
    refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
        (HRS.Whole.withDensityReal rho) beta N ≤
      ENNReal.ofReal (Real.exp (2 / 1000)) • HRS.Whole.withDensityReal rho := by
  haveI := c.prob
  rw [c.refMarg_eq hN1, c.unpinned_small hN1 hN,
    pairGibbsLawE_eq_pinnedLaw_E c.weak c.ha c.hbeta.le hN1]
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN1]
  have hm := HRS.External.RefMarg.marginal_le_smul (B := Empty) (mkV_E c.weak c.ha c.hbeta.le)
    c.hbeta.le hN1 (n := N) (by simp) (fun e : Empty => e.elim) ⟨0, hN1⟩
  refine hm.trans (s82r_smul_le _ (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
  show beta * wr13e_a d (criticalS d) tau M + 0 + beta * wr13e_a d (criticalS d) tau M ≤ 2 / 1000
  have := c.hsm
  linarith

theorem relL2_small (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN1 : 0 < N) (hN : N < N0) :
    eLpNorm (fun x => ((refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
      (HRS.Whole.withDensityReal rho) beta N).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal - 1) 2
      (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal (Real.exp (2 / 1000)) := by
  haveI := c.prob
  set ν := refMarginal (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
    (HRS.Whole.withDensityReal rho) beta N with hν
  have hle := c.refMarg_small_le hN1 hN
  haveI : IsFiniteMeasure ν := by
    refine ⟨lt_of_le_of_lt (hle Set.univ) ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  have hE1 : (1 : ℝ) ≤ Real.exp (2 / 1000) := Real.one_le_exp (by norm_num)
  have hrn := s82r_rnDeriv_le (by linarith) hle
  have hae : ∀ᵐ x ∂(HRS.Whole.withDensityReal rho),
      ‖((ν.rnDeriv (HRS.Whole.withDensityReal rho) x).toReal - 1)‖ ≤ Real.exp (2 / 1000) := by
    filter_upwards [hrn] with x hx
    rw [Real.norm_eq_abs, abs_le]
    have := ENNReal.toReal_nonneg (a := ν.rnDeriv (HRS.Whole.withDensityReal rho) x)
    constructor <;> linarith
  have hm : AEStronglyMeasurable (fun x => (ν.rnDeriv (HRS.Whole.withDensityReal rho) x).toReal - 1)
      (HRS.Whole.withDensityReal rho) :=
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub_const 1).aestronglyMeasurable
  have := eLpNorm_le_of_ae_bound (p := 2) hm hae
  simpa using this

/-- Relative `L^∞` smallness for the reference marginal. -/
theorem relative_small (c : S82RCtx d a beta rho M tau CR N0) :
    Tendsto (fun N => eLpNorm (fun x => ((refMarginal (qTau d (criticalS d) tau)
      (s82r_field d rho beta tau N0) (HRS.Whole.withDensityReal rho) beta N).rnDeriv
        (HRS.Whole.withDensityReal rho) x).toReal - 1) ∞ (HRS.Whole.withDensityReal rho)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun N => by rw [hεt]; exact le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  obtain ⟨N1, hN1⟩ := c.hUnif ε.toReal hεr
  filter_upwards [eventually_ge_atTop (max N0 N1)] with N hN
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hN1' : N1 ≤ N := (le_max_right _ _).trans hN
  rw [c.refMarg_large hN0]
  rw [eLpNorm_exponent_top]
  · refine (eLpNormEssSup_le_of_ae_bound (C := ε.toReal) ?_).trans (le_of_eq (ENNReal.ofReal_toReal hεt))
    filter_upwards [hN1 N hN1'] with x hx
    rwa [Real.norm_eq_abs]
  · exact ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub_const 1).aestronglyMeasurable

end S82RCtx

end HRS.MS.S82R

end
