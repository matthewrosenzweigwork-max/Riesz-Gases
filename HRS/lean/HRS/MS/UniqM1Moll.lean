import HRS.MS.UniqM1

/-!
# M1 of `UniqPlan.md`, part 2: the mollifier family `η_ε` and the smoothness of `η_ε * u`

`bump d : ContDiffBump (0 : Euc d)` has radii `1/2, 1`; `eta1 d := (bump d).normed volume`;
`eta d ε x := ε^{-d} η(x/ε)`.  Properties for `ε > 0`: `eta_contDiff` (`C^∞`), `eta_nonneg`,
`eta_support` (`⊆ ball 0 ε`), `eta_hasCompactSupport`, `eta_neg` (even), `integral_eta` (`= 1`),
`eta_le` (`|η_ε| ≤ C ε^{-d}`, `C = C(d)`).

`moll d ε u x := ∫ y, η_ε(x - y) u(y)`.  `moll_contDiff`: smooth for locally integrable `u`;
`moll_iteratedFDeriv_le`: for `LocMass B u` the `k`-th derivative is bounded by `C_k(ε) B`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.UniqM1

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### The mollifier family -/

/-- The bump function with radii `1/2` and `1`. -/
def bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The normalized bump: `C^∞`, `≥ 0`, support `ball 0 1`, integral `1`, even. -/
def eta1 (d : ℕ) : Euc d → ℝ := (bump d).normed volume

/-- The mollifier `η_ε(x) = ε^{-d} η(x/ε)`. -/
def eta (d : ℕ) (ε : ℝ) (x : Euc d) : ℝ := (ε ^ d)⁻¹ * eta1 d (ε⁻¹ • x)

theorem eta1_nonneg (x : Euc d) : 0 ≤ eta1 d x := (bump d).nonneg_normed x

theorem eta1_contDiff : ContDiff ℝ ∞ (eta1 d) := (bump d).contDiff_normed

theorem eta1_support : Function.support (eta1 d) = ball 0 1 := (bump d).support_normed_eq

theorem eta1_hasCompactSupport : HasCompactSupport (eta1 d) := (bump d).hasCompactSupport_normed

theorem eta_nonneg {ε : ℝ} (hε : 0 < ε) (x : Euc d) : 0 ≤ eta d ε x := by
  unfold eta; have := eta1_nonneg (d := d) (ε⁻¹ • x); positivity

theorem eta_contDiff {ε : ℝ} : ContDiff ℝ ∞ (eta d ε) := by
  unfold eta
  exact contDiff_const.mul (eta1_contDiff.comp (contDiff_id.const_smul ε⁻¹))

theorem eta_support {ε : ℝ} (hε : 0 < ε) : Function.support (eta d ε) ⊆ ball 0 ε := by
  intro x hx
  have h : eta1 d (ε⁻¹ • x) ≠ 0 := by
    intro h0; apply hx; unfold eta; rw [h0, mul_zero]
  have h' : ε⁻¹ • x ∈ ball (0 : Euc d) 1 := by rw [← eta1_support]; exact h
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε] at h'
  rw [mem_ball_zero_iff]
  have := mul_lt_mul_of_pos_left h' hε
  rwa [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one] at this

theorem eta_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (eta d ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) ε) ?_
  exact (eta_support hε).trans ball_subset_closedBall

theorem eta_tsupport {ε : ℝ} (hε : 0 < ε) : tsupport (eta d ε) ⊆ closedBall 0 ε := by
  refine closure_minimal ((eta_support hε).trans ball_subset_closedBall) isClosed_closedBall

theorem eta_neg (ε : ℝ) (x : Euc d) : eta d ε (-x) = eta d ε x := by
  unfold eta eta1
  rw [smul_neg, (bump d).normed_neg]

theorem integral_eta {ε : ℝ} (hε : 0 < ε) : ∫ x, eta d ε x = 1 := by
  unfold eta
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (eta1 d) hε.le]
  have h1 : ∫ x, eta1 d x = 1 := (bump d).integral_normed
  rw [finrank_euclideanSpace_fin, h1, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_pos hε d).ne']

theorem eta_le_aux : ∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, eta1 d x ≤ C := by
  refine ⟨(∫ x, (bump d) x)⁻¹, inv_pos.2 ((bump d).integral_pos (μ := (volume : Measure (Euc d)))), fun x => ?_⟩
  unfold eta1 ContDiffBump.normed
  rw [div_eq_mul_inv]
  have := (bump d).le_one (x := x)
  have h2 := (inv_pos.2 ((bump d).integral_pos (μ := (volume : Measure (Euc d))))).le
  calc (bump d) x * (∫ x, (bump d) x)⁻¹ ≤ 1 * (∫ x, (bump d) x)⁻¹ := by gcongr
    _ = _ := one_mul _

/-- `|η_ε| ≤ C ε^{-d}` with `C = C(d)`. -/
theorem eta_le : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ x : Euc d, |eta d ε x| ≤ C * (ε ^ d)⁻¹ := by
  obtain ⟨C, hC, h⟩ := eta_le_aux (d := d)
  refine ⟨C, hC, fun ε hε x => ?_⟩
  rw [abs_of_nonneg (eta_nonneg hε x)]
  unfold eta
  rw [mul_comm]
  gcongr
  exact h _

/-! ### Local integrability from `LocMass` -/

theorem LocMass.integrableOn_ball {B : ℝ} {u : Euc d → ℝ} (h : LocMass B u) (c : Euc d) (r : ℝ) :
    IntegrableOn u (ball c r) volume := by
  obtain ⟨K, -, hK⟩ := exists_ball_l1_bound d r
  refine ⟨h.1.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (hK |B| u (abs_nonneg B) (h.mono_B (by simp)) c).trans_lt ENNReal.ofReal_lt_top

theorem LocMass.locallyIntegrable {B : ℝ} {u : Euc d → ℝ} (h : LocMass B u) :
    LocallyIntegrable u volume := fun x =>
  ⟨ball x 1, ball_mem_nhds x one_pos, h.integrableOn_ball x 1⟩

/-- `∫_{closedBall c ε} |u| ≤ K B` (real form of the `L¹` mass bound). -/
theorem exists_closedBall_l1_real (d : ℕ) (ε : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → LocMass B u → ∀ c : Euc d,
      ∫ y in closedBall c ε, ‖u y‖ ≤ K * B := by
  obtain ⟨K, hK0, hK⟩ := exists_ball_l1_bound d (ε + 1)
  refine ⟨K, hK0, fun B u hB hu c => ?_⟩
  have hsub : closedBall c ε ⊆ ball c (ε + 1) := fun y hy => by
    rw [mem_closedBall] at hy; rw [mem_ball]; linarith
  have hint : IntegrableOn (fun y => ‖u y‖) (closedBall c ε) volume :=
    ((hu.integrableOn_ball c (ε + 1)).mono_set hsub).norm
  rw [integral_norm_eq_lintegral_enorm hu.1.restrict]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  exact (lintegral_mono_set hsub).trans (hK B u hB hu c)

/-! ### Convolution with vector-valued compactly supported smooth kernels -/

section Conv

/-- `F →L ℝ →L F`, `(a, r) ↦ r • a`. -/
def Lf (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] : F →L[ℝ] ℝ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip

/-- The convolution `G * u` of an `F`-valued kernel with a scalar function. -/
def cv (u : Euc d → ℝ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Euc d → F) :
    Euc d → F := G ⋆[Lf F, volume] u

theorem cv_apply (u : Euc d → ℝ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Euc d → F) (x : Euc d) : cv u G x = ∫ y, u y • G (x - y) := by
  unfold cv
  rw [convolution_eq_swap]
  rfl

theorem hasFDerivAt_cv {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : Euc d → F}
    (hc : HasCompactSupport G) (hG : ContDiff ℝ 1 G) (x : Euc d) :
    HasFDerivAt (cv u G) (cv u (fun t => fderiv ℝ G t) x) x := by
  have h := hc.hasFDerivAt_convolution_left (Lf F) hG hu x
  have e : cv u (fun t => fderiv ℝ G t) x =
      (fderiv ℝ G ⋆[(Lf F).precompL (Euc d), volume] u) x := by
    unfold cv
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ext v
    simp [Lf]
  rw [e]
  exact h

theorem fderiv_cv {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : Euc d → F}
    (hc : HasCompactSupport G) (hG : ContDiff ℝ 1 G) :
    fderiv ℝ (cv u G) = cv u (fun t => fderiv ℝ G t) :=
  funext fun x => (hasFDerivAt_cv hu hc hG x).fderiv

theorem contDiff_cv {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : Euc d → F}
    (hc : HasCompactSupport G) (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (cv u G) :=
  hc.contDiff_convolution_left (Lf F) hG hu

/-- Derivative bounds for `G * u`: if `tsupport G ⊆ closedBall 0 ε`, `‖D^k G‖ ≤ M` and the `L¹`
mass of `u` on every `ε`-ball is `≤ m`, then `‖D^k (G * u)‖ ≤ M m`. -/
theorem iteratedFDeriv_cv_le {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) {ε m : ℝ}
    (hm : ∀ x : Euc d, ∫ y in closedBall x ε, ‖u y‖ ≤ m) (k : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : Euc d → F),
      HasCompactSupport G → ContDiff ℝ ∞ G → tsupport G ⊆ closedBall 0 ε → ∀ M : ℝ,
      (∀ t, ‖iteratedFDeriv ℝ k G t‖ ≤ M) → ∀ x, ‖iteratedFDeriv ℝ k (cv u G) x‖ ≤ M * m := by
  induction k with
  | zero =>
    intro F _ _ _ G hc hG hts M hM x
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hG0 : ∀ t, ‖G t‖ ≤ M := fun t => by simpa using hM t
    rw [norm_iteratedFDeriv_zero, cv_apply]
    have hint : IntegrableOn (fun y => ‖u y‖) (closedBall x ε) volume :=
      (hu.integrableOn_isCompact (isCompact_closedBall x ε)).norm
    have hbd : Integrable ((closedBall x ε).indicator fun y => M * ‖u y‖) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2 (hint.const_mul M)
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun y => ?_)).trans ?_
    · by_cases hy : y ∈ closedBall x ε
      · rw [Set.indicator_of_mem hy, norm_smul]
        calc ‖u y‖ * ‖G (x - y)‖ ≤ ‖u y‖ * M := by gcongr; exact hG0 _
          _ = M * ‖u y‖ := mul_comm _ _
      · rw [Set.indicator_of_notMem hy]
        have : G (x - y) = 0 := by
          by_contra hne
          apply hy
          have := hts (subset_tsupport _ hne)
          rw [mem_closedBall_zero_iff] at this
          rw [mem_closedBall, dist_comm, dist_eq_norm]; exact this
        simp [this]
    · rw [integral_indicator measurableSet_closedBall, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hm x) hM0
  | succ k ih =>
    intro F _ _ _ G hc hG hts M hM x
    rw [← norm_iteratedFDeriv_fderiv, fderiv_cv hu hc (hG.of_le (by simp))]
    refine ih (Euc d →L[ℝ] F) (fun t => fderiv ℝ G t) ?_ ?_ ?_ M ?_ x
    · exact hc.fderiv ℝ
    · exact hG.fderiv_right (by simp)
    · exact (tsupport_fderiv_subset ℝ).trans hts
    · intro t; rw [norm_iteratedFDeriv_fderiv]; exact hM t

end Conv

end HRS.MS.UniqM1
