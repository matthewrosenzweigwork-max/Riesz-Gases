import HRS.MS.UniqE4a

/-!
# E4 of `UniqPlan.md`, part 2: weak-gradient identity for decaying `C¹` tests, integration by parts,
and the Fubini swap for the mollifier

* `e4_weak_decay` : `∫ u ∂_jΘ = -∫ v_j Θ` for `Θ ∈ C¹` with `|Θ|, |∂_jΘ| ≤ M ⟨x⟩^{-κ}`, `κ > d`
  (cut off by a fixed bump at radius `R` and let `R → ∞`).
* `e4_ibp_decay` : `∫ f ∂_jG = -∫ ∂_jf G` for `f` bounded `C¹` with bounded derivative and `G` decaying.
* `e4_swap_moll` : `∫ f (η_ε * G) = ∫ (η_ε * f) G` for `f ∈ L¹`, `G` bounded measurable.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

/-! ### The cutoffs -/

/-- `β_R(y) = b(y / R)` for the fixed bump `b = bump d` (`b = 1` on `B̄(0,1/2)`, `b = 0` off `B(0,1)`). -/
def cutR (d : ℕ) (R : ℝ) (y : Euc d) : ℝ := bump d (R⁻¹ • y)

theorem cutR_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutR d R) :=
  show ContDiff ℝ ∞ (fun y : Euc d => bump d (R⁻¹ • y)) from
    (bump d).contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem cutR_range (R : ℝ) (y : Euc d) : 0 ≤ cutR d R y ∧ cutR d R y ≤ 1 :=
  ⟨(bump d).nonneg, (bump d).le_one⟩

theorem cutR_one {R : ℝ} (hR : 0 < R) {y : Euc d} (hy : ‖y‖ ≤ R / 2) : cutR d R y = 1 := by
  unfold cutR
  apply (bump d).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  have : (bump d).rIn = 1 / 2 := rfl
  rw [this, inv_mul_le_iff₀ hR]
  linarith

theorem cutR_zero {R : ℝ} (hR : 0 < R) {y : Euc d} (hy : R ≤ ‖y‖) : cutR d R y = 0 := by
  unfold cutR
  apply (bump d).zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  have : (bump d).rOut = 1 := rfl
  rw [this, le_inv_mul_iff₀ hR]
  linarith

theorem cutR_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutR d R) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) R) ?_
  intro y hy
  rw [mem_closedBall_zero_iff]
  by_contra hcon
  exact hy (cutR_zero hR (not_le.1 hcon).le)

theorem cutR_D1 {R : ℝ} (hR : 0 < R) (j : Fin d) (y : Euc d) :
    D1 j (cutR d R) y = R⁻¹ * D1 j (bump d) (R⁻¹ • y) := by
  have h1 : HasFDerivAt (fun y : Euc d => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) y :=
    (hasFDerivAt_id y).const_smul R⁻¹
  have h2 := (((bump d).contDiff (n := 1)).differentiable (by simp) (R⁻¹ • y)).hasFDerivAt.comp y h1
  unfold D1 cutR
  have := h2.fderiv
  show fderiv ℝ ((bump d) ∘ fun y : Euc d => R⁻¹ • y) y (EuclideanSpace.single j 1) = _
  rw [this]
  simp

theorem exists_bump_deriv_bound (d : ℕ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (j : Fin d) (x : Euc d), |D1 j (bump d) x| ≤ Kb := by
  have hc : Continuous (fderiv ℝ (bump d)) := ((bump d).contDiff (n := 1)).continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support ((bump d).hasCompactSupport.fderiv ℝ)
  refine ⟨max M 0, le_max_right _ _, fun j x => ?_⟩
  exact (e3_abs_apply_le _ j).trans ((hM x).trans (le_max_left _ _))

theorem cutR_D1_bound {R : ℝ} (hR : 0 < R) {Kb : ℝ} (hKb : ∀ (j : Fin d) (x : Euc d),
    |D1 j (bump d) x| ≤ Kb) (j : Fin d) (y : Euc d) : |D1 j (cutR d R) y| ≤ R⁻¹ * Kb := by
  rw [cutR_D1 hR, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_left (hKb j _) (inv_pos.2 hR).le

/-! ### Integrability against decaying functions -/

theorem e4_norm_mul_le {a b c : ℝ} (hb : |b| ≤ 1) : ‖a * (b * c)‖ ≤ ‖a * c‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  calc |a| * (|b| * |c|) ≤ |a| * (1 * |c|) := by gcongr
    _ = |a| * |c| := by ring

theorem e4_decay_integrable {κ : ℝ} (hκ : (d : ℝ) < κ) {M : ℝ} {h : Euc d → ℝ}
    (hh : AEStronglyMeasurable h volume) (hb : ∀ y, |h y| ≤ M * (1 + ‖y‖) ^ (-κ)) :
    Integrable h volume := by
  have hi := (n0_decay_integrable hκ (0 : Euc d)).const_mul M
  refine hi.mono' hh (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  simpa using hb y

/-- The weak-gradient identity for decaying `C¹` tests. -/
theorem e4_weak_decay {κ : ℝ} (hκ : (d : ℝ) < κ) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {v : Euc d → Euc d} (hv : IsWeakGrad u v) (j : Fin d) (hvj : LocMass B (fun x => v x j))
    {Θ : Euc d → ℝ} (hΘ : ContDiff ℝ 1 Θ) {M : ℝ}
    (hΘ0 : ∀ y, |Θ y| ≤ M * (1 + ‖y‖) ^ (-κ))
    (hΘ1 : ∀ y, |D1 j Θ y| ≤ M * (1 + ‖y‖) ^ (-κ)) :
    ∫ x, u x * D1 j Θ x = - ∫ x, v x j * Θ x := by
  have hM : 0 ≤ M := by
    have := hΘ0 0
    simp at this
    exact (abs_nonneg _).trans this
  obtain ⟨C, hC0, hC⟩ := n0_cell_decay_mul (d := d) hκ
  have hDc : Continuous (D1 j Θ) := e3_continuous_D1 hΘ j
  have hI1 : Integrable (fun y => u y * D1 j Θ y) volume :=
    ((hC 0 M B u (D1 j Θ) hM hu (by simpa using hΘ1)).2 hDc.aestronglyMeasurable).1
  have hI2 : Integrable (fun y => v y j * Θ y) volume :=
    ((hC 0 M B (fun x => v x j) Θ hM hvj (by simpa using hΘ0)).2
      hΘ.continuous.aestronglyMeasurable).1
  have hI3 : Integrable (fun y => u y * Θ y) volume :=
    ((hC 0 M B u Θ hM hu (by simpa using hΘ0)).2 hΘ.continuous.aestronglyMeasurable).1
  obtain ⟨Kb, hKb0, hKb⟩ := exists_bump_deriv_bound d
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1 with hR
  have hRpos : ∀ n, 0 < R n := fun n => by simp only [hR]; positivity
  set β : ℕ → Euc d → ℝ := fun n => cutR d (R n) with hβ
  have hΘn : ∀ n, ContDiff ℝ 1 (fun y => β n y * Θ y) := fun n =>
    ((cutR_contDiff (R n)).of_le (by simp)).mul hΘ
  have hΘnc : ∀ n, HasCompactSupport (fun y => β n y * Θ y) := fun n =>
    (cutR_compact (hRpos n)).mul_right
  have hLoc1 : LocallyIntegrable u volume := hu.locallyIntegrable
  have hLoc2 : LocallyIntegrable (fun x => v x j) volume := hvj.locallyIntegrable
  have hid : ∀ n, ∫ x, u x * D1 j (fun y => β n y * Θ y) x =
      - ∫ x, v x j * (β n x * Θ x) := fun n =>
    e4_weak_c1 hLoc1 hv j hLoc2 (hΘn n) (hΘnc n)
  have hprod : ∀ n x, D1 j (fun y => β n y * Θ y) x =
      β n x * D1 j Θ x + Θ x * D1 j (β n) x := fun n x =>
    e3_D1_mul ((cutR_contDiff (R n)).differentiable (by simp))
      (hΘ.differentiable (by simp)) j x
  -- integrability of the pieces
  have hbd : ∀ n x, |β n x| ≤ 1 := fun n x => by
    rw [abs_of_nonneg (cutR_range _ x).1]; exact (cutR_range _ x).2
  have hmeasβ : ∀ n, Continuous (β n) := fun n => (cutR_contDiff (R n)).continuous
  have hJ1 : ∀ n, Integrable (fun x => u x * (β n x * D1 j Θ x)) volume := fun n =>
    hI1.norm.mono' (hLoc1.aestronglyMeasurable.mul ((hmeasβ n).mul hDc).aestronglyMeasurable)
      (Eventually.of_forall fun x => e4_norm_mul_le (hbd n x))
  have hJ3 : ∀ n, Integrable (fun x => v x j * (β n x * Θ x)) volume := fun n =>
    hI2.norm.mono' (hLoc2.aestronglyMeasurable.mul ((hmeasβ n).mul hΘ.continuous).aestronglyMeasurable)
      (Eventually.of_forall fun x => e4_norm_mul_le (hbd n x))
  have hDβ : ∀ n x, |D1 j (β n) x| ≤ (R n)⁻¹ * Kb := fun n x => cutR_D1_bound (hRpos n) hKb j x
  have hDβc : ∀ n, Continuous (D1 j (β n)) := fun n =>
    e3_continuous_D1 ((cutR_contDiff (R n)).of_le (by simp)) j
  have hJ2 : ∀ n, Integrable (fun x => u x * (Θ x * D1 j (β n) x)) volume := fun n => by
    refine (hI3.norm.const_mul ((R n)⁻¹ * Kb)).mono'
      (hLoc1.aestronglyMeasurable.mul (hΘ.continuous.mul (hDβc n)).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    calc |u x| * (|Θ x| * |D1 j (β n) x|) ≤ |u x| * (|Θ x| * ((R n)⁻¹ * Kb)) := by
          gcongr; exact hDβ n x
      _ = _ := by ring
  have hsplit : ∀ n, (∫ x, u x * (β n x * D1 j Θ x)) + (∫ x, u x * (Θ x * D1 j (β n) x)) =
      - ∫ x, v x j * (β n x * Θ x) := fun n => by
    rw [← integral_add (hJ1 n) (hJ2 n), ← hid n]
    congr 1; funext x
    rw [hprod n x]; ring
  -- limits
  have hlim : ∀ x : Euc d, Tendsto (fun n => β n x) atTop (𝓝 1) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨⌈2 * ‖x‖⌉₊, fun n hn => (cutR_one (hRpos n) ?_).symm⟩
    have h1 : 2 * ‖x‖ ≤ (⌈2 * ‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * ‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hR]; linarith
  have T1 : Tendsto (fun n => ∫ x, u x * (β n x * D1 j Θ x)) atTop (𝓝 (∫ x, u x * D1 j Θ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x * D1 j Θ x‖)
      (fun n => (hJ1 n).aestronglyMeasurable) hI1.norm
      (fun n => Eventually.of_forall fun x => e4_norm_mul_le (hbd n x))
      (Eventually.of_forall fun x => ?_)
    have := (((hlim x).mul_const (D1 j Θ x)).const_mul (u x))
    simpa using this
  have T3 : Tendsto (fun n => ∫ x, v x j * (β n x * Θ x)) atTop (𝓝 (∫ x, v x j * Θ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖v x j * Θ x‖)
      (fun n => (hJ3 n).aestronglyMeasurable) hI2.norm
      (fun n => Eventually.of_forall fun x => e4_norm_mul_le (hbd n x))
      (Eventually.of_forall fun x => ?_)
    have := (((hlim x).mul_const (Θ x)).const_mul (v x j))
    simpa using this
  have T2 : Tendsto (fun n => ∫ x, u x * (Θ x * D1 j (β n) x)) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun n : ℕ => (R n)⁻¹ * Kb * ∫ x, ‖u x * Θ x‖) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (h.mul_const Kb).mul_const (∫ x, ‖u x * Θ x‖)
      simp only [zero_mul] at h2
      refine h2.congr (fun n => ?_)
      simp only [hR, one_div]
    refine squeeze_zero_norm (fun n => ?_) hb0
    refine (norm_integral_le_of_norm_le (hI3.norm.const_mul ((R n)⁻¹ * Kb))
      (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
    · simp only [Real.norm_eq_abs, abs_mul]
      calc |u x| * (|Θ x| * |D1 j (β n) x|) ≤ |u x| * (|Θ x| * ((R n)⁻¹ * Kb)) := by
            gcongr; exact hDβ n x
        _ = _ := by ring
    · rw [integral_const_mul]
  have T4 : Tendsto (fun n => ∫ x, u x * (β n x * D1 j Θ x)) atTop
      (𝓝 (-(∫ x, v x j * Θ x))) := by
    have := (T3.neg).sub T2
    rw [sub_zero] at this
    refine this.congr (fun n => ?_)
    have := hsplit n
    linarith
  have := tendsto_nhds_unique T1 T4
  linarith

/-- Integration by parts against a decaying `C¹` function. -/
theorem e4_ibp_decay {κ : ℝ} (hκ : (d : ℝ) < κ) {f G : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hG : ContDiff ℝ 1 G) (j : Fin d) {Mf : ℝ} (hf0 : ∀ x, |f x| ≤ Mf) (hf1 : ∀ x, |D1 j f x| ≤ Mf)
    {M : ℝ} (hG0 : ∀ y, |G y| ≤ M * (1 + ‖y‖) ^ (-κ))
    (hG1 : ∀ y, |D1 j G y| ≤ M * (1 + ‖y‖) ^ (-κ)) :
    ∫ x, f x * D1 j G x = - ∫ x, D1 j f x * G x := by
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hf0 0)
  have hfc := hf.continuous
  have hGc := hG.continuous
  have hDf := e3_continuous_D1 hf j
  have hDG := e3_continuous_D1 hG j
  have b1 : Integrable (fun x => D1 j f x * G x) volume :=
    e4_decay_integrable (M := Mf * M) hκ (hDf.mul hGc).aestronglyMeasurable fun y => by
      rw [abs_mul]
      calc |D1 j f y| * |G y| ≤ Mf * (M * (1 + ‖y‖) ^ (-κ)) :=
            mul_le_mul (hf1 y) (hG0 y) (abs_nonneg _) hMf
        _ = _ := by ring
  have b2 : Integrable (fun x => f x * D1 j G x) volume :=
    e4_decay_integrable (M := Mf * M) hκ (hfc.mul hDG).aestronglyMeasurable fun y => by
      rw [abs_mul]
      calc |f y| * |D1 j G y| ≤ Mf * (M * (1 + ‖y‖) ^ (-κ)) :=
            mul_le_mul (hf0 y) (hG1 y) (abs_nonneg _) hMf
        _ = _ := by ring
  have b3 : Integrable (fun x => f x * G x) volume :=
    e4_decay_integrable (M := Mf * M) hκ (hfc.mul hGc).aestronglyMeasurable fun y => by
      rw [abs_mul]
      calc |f y| * |G y| ≤ Mf * (M * (1 + ‖y‖) ^ (-κ)) :=
            mul_le_mul (hf0 y) (hG0 y) (abs_nonneg _) hMf
        _ = _ := by ring
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := EuclideanSpace.single j (1 : ℝ))
    b1 b2 b3 (fun x _ => hf.differentiable (by simp) x) (fun x _ => hG.differentiable (by simp) x)

/-- Fubini swap for the mollifier: `∫ f (η_ε * G) = ∫ (η_ε * f) G`. -/
theorem e4_swap_moll {ε : ℝ} (hε : 0 < ε) {f G : Euc d → ℝ} (hf : Integrable f volume)
    (hG : AEStronglyMeasurable G volume) {M : ℝ} (hGb : ∀ x, |G x| ≤ M) :
    Integrable (fun x => moll d ε f x * G x) volume ∧
      ∫ y, f y * moll d ε G y = ∫ x, moll d ε f x * G x := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hGb 0)
  set F : Euc d × Euc d → ℝ := fun p => f p.1 * (eta d ε (p.1 - p.2) * G p.2) with hF
  have hfm : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.1) (volume.prod volume) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hGm : AEStronglyMeasurable (fun p : Euc d × Euc d => G p.2) (volume.prod volume) :=
    hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hηm : Continuous (fun p : Euc d × Euc d => eta d ε (p.1 - p.2)) :=
    eta_contDiff.continuous.comp (continuous_fst.sub continuous_snd)
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    hfm.mul (hηm.aestronglyMeasurable.mul hGm)
  set g : Euc d × Euc d → ℝ := fun p => M * (‖f p.1‖ * eta d ε (p.1 - p.2)) with hg
  have hgm : AEStronglyMeasurable g (volume.prod volume) :=
    (hfm.norm.mul hηm.aestronglyMeasurable).const_mul M
  have hgi : Integrable g (volume.prod volume) := by
    rw [integrable_prod_iff hgm]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · simp only [hg]
      exact ((e4_eta_integrable hε y).const_mul ‖f y‖).const_mul M
    · have : ∀ y, ∫ x, ‖g (y, x)‖ = M * ‖f y‖ := by
        intro y
        have h0 : ∀ x, ‖g (y, x)‖ = (M * ‖f y‖) * eta d ε (y - x) := by
          intro x
          simp only [hg]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (mul_nonneg (norm_nonneg _)
            (eta_nonneg hε _)))]
          ring
        simp_rw [h0]
        rw [integral_const_mul, e4_integral_eta_sub hε, mul_one]
      simp_rw [this]
      exact hf.norm.const_mul M
  have hFi : Integrable F (volume.prod volume) := by
    refine hgi.mono' hFm (Eventually.of_forall fun p => ?_)
    simp only [hF, hg]
    rw [norm_mul, norm_mul, Real.norm_eq_abs (eta d ε _), abs_of_nonneg (eta_nonneg hε _),
      Real.norm_eq_abs (G _)]
    calc ‖f p.1‖ * (eta d ε (p.1 - p.2) * |G p.2|) ≤ ‖f p.1‖ * (eta d ε (p.1 - p.2) * M) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGb _) (eta_nonneg hε _)) (norm_nonneg _)
      _ = _ := by ring
  have e1 : ∀ y, ∫ x, F (y, x) = f y * moll d ε G y := fun y => by
    simp only [hF]
    rw [integral_const_mul]; rfl
  have e2 : ∀ x, ∫ y, F (y, x) = moll d ε f x * G x := fun x => by
    simp only [hF]
    unfold moll
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← eta_neg ε (x - y), neg_sub]; ring
  refine ⟨?_, ?_⟩
  · have := hFi.integral_prod_right
    exact this.congr (Eventually.of_forall fun x => by simp only [e2])
  · have := integral_integral_swap (f := fun y x => F (y, x)) hFi
    simp_rw [e1, e2] at this
    exact this

end HRS.MS.UniqE4
