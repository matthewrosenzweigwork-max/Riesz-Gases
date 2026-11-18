import HRS.MS.S82RA1

/-!
# S8.2 R01A (S82R), part 2: the calibration context and the calibrated field
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wr HRS.MS.Psd

variable {d : ℕ}

lemma s82r_deltaN_eq (d N : ℕ) : HRS.deltaN d (criticalS d) N = HRS.MS.Phase2S82.deltaN N := by
  rw [HRS.Whole.deltaN_eq]
  have h1 : ¬ (criticalS d < (d : ℝ) / 2) := by unfold criticalS; exact lt_irrefl _
  have h2 : criticalS d = (d : ℝ) / 2 := rfl
  rw [if_neg h1, if_pos h2]
  unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN
  rw [div_eq_inv_mul]

lemma s82r_criticalS_pos (hd : 1 ≤ d) : 0 < criticalS d := by
  unfold criticalS
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma s82r_criticalS_lt (hd : 1 ≤ d) : criticalS d < d := by
  unfold criticalS
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- The calibrated field: `⟪t_N, Ξ⟫` for `N ≥ N0`, `0` below. -/
def s82r_field (d : ℕ) (rho : Euc d → ℝ) (beta tau : ℝ) (N0 : ℕ) (N : ℕ) (x : Euc d) : ℝ :=
  if N0 ≤ N then
    inner ℝ (tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
      (featMap d (criticalS d) tau) beta N)
      (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) x)
  else 0

/-- The standing facts about the calibrated reference at large `N`. -/
structure S82RCtx (d : ℕ) (a beta : ℝ) (rho : Euc d → ℝ) (M tau CR : ℝ) (N0 : ℕ) : Prop where
  hd : 2 ≤ d
  hbeta : 0 < beta
  hρ : HRS.Whole.IsProbDensity rho
  hM : ∀ x, rho x ≤ M
  htau : 0 < tau
  hsm : beta * wr13e_a d (criticalS d) tau M ≤ 1 / 1000
  hN0 : 2 ≤ N0
  hCR : 0 ≤ CR
  hfs : ∀ N, N0 ≤ N → ∀ x,
    |inner ℝ (tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
      (featMap d (criticalS d) tau) beta N)
      (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) x)| ≤ 1
  hL2 : ∀ N, N0 ≤ N →
    HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y))
      (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) beta N) ≪ HRS.Whole.withDensityReal rho ∧
    eLpNorm (fun y => ((HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y))
      (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) beta N)).rnDeriv
        (HRS.Whole.withDensityReal rho) y).toReal - 1) 2 (HRS.Whole.withDensityReal rho) ≤
      ENNReal.ofReal (CR * HRS.deltaN d (criticalS d) N)
  hUnif : ∀ ε : ℝ, 0 < ε → ∃ N1 : ℕ, ∀ N, N1 ≤ N → ∀ᵐ y ∂(HRS.Whole.withDensityReal rho),
    |((HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y))
      (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) beta N)).rnDeriv
        (HRS.Whole.withDensityReal rho) y).toReal - 1| ≤ ε
  hcan : ∀ N, canonicalP d N a beta =
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d (criticalS d)) N beta (HRS.Whole.withDensityReal rho)

namespace S82RCtx

variable {a beta : ℝ} {rho : Euc d → ℝ} {M tau CR : ℝ} {N0 : ℕ}

theorem hd1 (c : S82RCtx d a beta rho M tau CR N0) : 1 ≤ d := by have := c.hd; omega

theorem prob (c : S82RCtx d a beta rho M tau CR N0) : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
  HRS.Whole.Q34.isProbabilityMeasure_nu c.hρ

theorem weak (c : S82RCtx d a beta rho M tau CR N0) :
    EWeakKernel (HRS.Whole.withDensityReal rho) (wr13e_a d (criticalS d) tau M)
      (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) :=
  wr13e_weak c.hd1 (s82r_criticalS_pos c.hd1) (s82r_criticalS_lt c.hd1) c.htau c.hρ c.hM

theorem ha (c : S82RCtx d a beta rho M tau CR N0) : 0 ≤ wr13e_a d (criticalS d) tau M :=
  wr13e_a_nonneg (s82r_criticalS_pos c.hd1) (s82r_criticalS_lt c.hd1) c.htau M

theorem trans (c : S82RCtx d a beta rho M tau CR N0) :
    TransferHyp (HRS.Whole.withDensityReal rho) (wr13e_a d (criticalS d) tau M) (qTau d (criticalS d) tau)
      (kTau d (criticalS d) tau) (HRS.Whole.rieszKernel d (criticalS d)) (featMap d (criticalS d) tau) :=
  wr14a_transferHyp c.hd1 (s82r_criticalS_pos c.hd1) (s82r_criticalS_lt c.hd1) c.htau c.hρ c.hM

theorem calfeat (c : S82RCtx d a beta rho M tau CR N0) :
    CalFeat (featMap d (criticalS d) tau) (Real.sqrt (kTau d (criticalS d) tau 0)) :=
  wr13e_calFeat (featMap_hyp (s82r_criticalS_pos c.hd1) c.htau)

theorem field_of_le (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) (x : Euc d) :
    s82r_field d rho beta tau N0 N x =
      inner ℝ (tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
        (featMap d (criticalS d) tau) beta N)
        (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) x) := by
  unfold s82r_field; rw [if_pos hN]

theorem field_of_lt (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N < N0) (x : Euc d) :
    s82r_field d rho beta tau N0 N x = 0 := by
  unfold s82r_field; rw [if_neg (not_le.2 hN)]

theorem field_meas (c : S82RCtx d a beta rho M tau CR N0) (N : ℕ) :
    Measurable (s82r_field d rho beta tau N0 N) := by
  haveI := c.prob
  by_cases hN : N0 ≤ N
  · have : s82r_field d rho beta tau N0 N = fun x =>
        inner ℝ (tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
        (featMap d (criticalS d) tau) beta N)
        (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) x) :=
      funext fun x => c.field_of_le hN x
    rw [this]
    exact wr12b_measurable_inner_Xi c.calfeat _
  · have : s82r_field d rho beta tau N0 N = fun _ => 0 :=
      funext fun x => c.field_of_lt (not_le.1 hN) x
    rw [this]
    exact measurable_const

theorem field_le_one (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (x : Euc d) :
    |s82r_field d rho beta tau N0 N x| ≤ 1 := by
  by_cases hN : N0 ≤ N
  · rw [c.field_of_le hN]; exact c.hfs N hN x
  · rw [c.field_of_lt (not_le.1 hN)]; simp

theorem small_row (c : S82RCtx d a beta rho M tau CR N0) (x : Euc d) :
    beta * HRS.Whole.convMeasure (qTau d (criticalS d) tau) (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000 := by
  haveI := c.prob
  have h1 : HRS.Whole.convMeasure (qTau d (criticalS d) tau) (HRS.Whole.withDensityReal rho) x ≤
      wr13e_a d (criticalS d) tau M := c.weak.wr1_rowInt_le c.ha x
  exact (mul_le_mul_of_nonneg_left h1 c.hbeta.le).trans c.hsm

end S82RCtx

end HRS.MS.S82R

end
