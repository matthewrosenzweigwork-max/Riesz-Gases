import HRS.MS.S82RA2

/-!
# S8.2 R01A (S82R), part 3: identification of the unpinned reference, physical domination
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wr HRS.MS.Psd

variable {d : ℕ}

lemma s82r_smul_mono {α : Type*} [MeasurableSpace α] {ν ν' : Measure α} (h : ν ≤ ν') (c : ℝ≥0∞) :
    c • ν ≤ c • ν' := by
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_right (h s) _

lemma s82r_smul_smul_le {α : Type*} [MeasurableSpace α] {ν ν' ν'' : Measure α} {c c' : ℝ}
    (hc : 0 ≤ c) (h1 : ν ≤ ENNReal.ofReal c • ν') (h2 : ν' ≤ ENNReal.ofReal c' • ν'') :
    ν ≤ ENNReal.ofReal (c * c') • ν'' := by
  refine h1.trans ?_
  refine (s82r_smul_mono h2 _).trans (le_of_eq ?_)
  rw [smul_smul, ENNReal.ofReal_mul hc]

lemma s82r_one_thousand_le : (1 : ℝ) / 1000 ≤ 1 / (16 * Real.exp 3) := by
  have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 :=
    pow_lt_pow_left₀ h3 (Real.exp_pos _).le (by norm_num)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_pos 3]

open HRS.External in
lemma s82r_pinnedLaw_emptyA3 {μ : Measure (Euc d)} (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    pinnedLaw V lam n (fun e : Empty => e.elim) = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

namespace S82RCtx

variable {a beta : ℝ} {rho : Euc d → ℝ} {M tau CR : ℝ} {N0 : ℕ}

/-- Large `N`: the unpinned reference is the calibrated `R_N`. -/
theorem unpinned_large (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) :
    unpinnedReference (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
        (HRS.Whole.withDensityReal rho) beta N =
      RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
        (featMap d (criticalS d) tau) beta N := by
  haveI := c.prob
  have hN1 : 0 < N := by have := c.hN0; omega
  have ht := c.hfs N hN
  set V := wr13e_weakPotK c.weak c.ha c.hbeta.le c.calfeat
    (tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
      (featMap d (criticalS d) tau) beta N) ht with hV
  have hVφ : V.φ = s82r_phi (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
      (HRS.Whole.withDensityReal rho) beta N := by
    funext x
    rw [hV, wr13e_weakPotK_φ]
    unfold s82r_phi
    rw [c.field_of_le hN x]
    rfl
  have hVq : ∀ x y, V.q x y = qTau d (criticalS d) tau (x - y) := fun x y => rfl
  unfold unpinnedReference
  rw [s82r_referenceLaw_eq_pot V hVφ hVq c.hbeta.le, s82r_pinnedLaw_zero]
  exact (wr13e_RN_eq_fieldLawK c.weak c.ha c.hbeta.le c.calfeat hN1 ht).symm

/-- Small `N`: the unpinned reference is the zero-field pair Gibbs law. -/
theorem unpinned_small (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN1 : 0 < N) (hN : N < N0) :
    unpinnedReference (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
        (HRS.Whole.withDensityReal rho) beta N =
      pairGibbsLawE (fun x y : Euc d => qTau d (criticalS d) tau (x - y))
        N beta (HRS.Whole.withDensityReal rho) := by
  haveI := c.prob
  set V := mkV_E c.weak c.ha c.hbeta.le with hV
  have hVφ : V.φ = s82r_phi (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
      (HRS.Whole.withDensityReal rho) beta N := by
    funext x
    unfold s82r_phi
    rw [c.field_of_lt hN x, add_zero]
    rfl
  have hVq : ∀ x y, V.q x y = qTau d (criticalS d) tau (x - y) := fun x y => rfl
  unfold unpinnedReference
  rw [s82r_referenceLaw_eq_pot V hVφ hVq c.hbeta.le, s82r_pinnedLaw_zero,
    pairGibbsLawE_eq_pinnedLaw_E c.weak c.ha c.hbeta.le hN1, s82r_pinnedLaw_emptyA3]

/-- Domination for large `N`. -/
theorem dom_large (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) :
    canonicalP d N a beta ≤
      ENNReal.ofReal (Real.exp (4 * beta * kTau d (criticalS d) tau 0)) •
        unpinnedReference (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
          (HRS.Whole.withDensityReal rho) beta N := by
  haveI := c.prob
  haveI := featMap_separableSpace (d := d) (s82r_criticalS_pos c.hd1) c.htau
  have hN1 : 0 < N := by have := c.hN0; omega
  rw [c.hcan N, c.unpinned_large hN]
  have hκ : wr11b_KappaSmall beta (wr13e_a d (criticalS d) tau M) := by
    have h0 : 0 ≤ beta * wr13e_a d (criticalS d) tau M := mul_nonneg c.hbeta.le c.ha
    exact wr11b_kappaSmall_of_le h0 (c.hsm.trans s82r_one_thousand_le)
  exact Q_le_smul_RN c.trans c.hbeta hN1 (c.hfs N hN) hκ

/-- Domination for small `N` (crude). -/
theorem dom_small (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN1 : 0 < N) (hN : N < N0) :
    canonicalP d N a beta ≤
      ENNReal.ofReal (Real.exp (16 * beta * N * kTau d (criticalS d) tau 0)) •
        unpinnedReference (qTau d (criticalS d) tau) (s82r_field d rho beta tau N0)
          (HRS.Whole.withDensityReal rho) beta N := by
  haveI := c.prob
  haveI := featMap_separableSpace (d := d) (s82r_criticalS_pos c.hd1) c.htau
  rw [c.hcan N, c.unpinned_small hN1 hN]
  set k0 := kTau d (criticalS d) tau 0 with hk0
  have hk0n : 0 ≤ k0 := kTau_nonneg (s82r_criticalS_pos c.hd1) c.htau 0
  have hQ := wr14a_Q_le_crude c.trans c.hbeta hN1
  set t := tN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
    (featMap d (criticalS d) tau) beta N with ht
  have hYb : ∀ X : Fin N → Euc d,
      |Yf (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) t X| ≤ 4 * beta * N * k0 := by
    intro X
    unfold Yf
    calc |∑ i, inner ℝ t (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) (X i))|
        ≤ ∑ i, |inner ℝ t (Xi (HRS.Whole.withDensityReal rho) (featMap d (criticalS d) tau) (X i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 4 * beta * k0 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := wr13e_abs_tN_inner_le c.weak c.calfeat c.hbeta hN1 (X i)
          rw [Real.sq_sqrt hk0n] at this
          exact this
      _ = 4 * beta * N * k0 := by simp; ring
  have hRN : RN (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) (HRS.Whole.withDensityReal rho)
      (featMap d (criticalS d) tau) beta N ≤
      ENNReal.ofReal (Real.exp (2 * (4 * beta * N * k0))) •
        pairGibbsLawE (fun x y : Euc d => qTau d (criticalS d) tau (x - y)) N beta
          (HRS.Whole.withDensityReal rho) := by
    haveI := c.weak.wr11_isProb_R0 c.hbeta.le hN1
    exact s82r_tilted_le _ _ (c.calfeat.measurable_Yf t) hYb
  have := s82r_smul_smul_le (Real.exp_pos _).le hQ hRN
  refine this.trans (le_of_eq ?_)
  congr 3
  rw [← Real.exp_add]
  congr 1
  ring

end S82RCtx

end HRS.MS.S82R

end
