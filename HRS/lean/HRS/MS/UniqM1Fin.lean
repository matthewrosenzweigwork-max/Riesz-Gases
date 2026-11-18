import HRS.MS.UniqM1Moll

/-!
# M1 of `UniqPlan.md`, part 3: `z_ε = η_ε * u`

* `moll_contDiff`, `moll_iteratedFDeriv_le`: smoothness and derivative bounds `C_k(ε) B`.
* `integral_moll_mul`: `∫ z_ε ψ = ∫ u (η_ε * ψ)` (Fubini).
* `moll_mass_le`: `∫_{ball c r} z_ε² ≤ ∫_{ball c (r+ε)} u²`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.UniqM1

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The mollification `z_ε(x) = ∫ η_ε(x - y) u(y) dy`. -/
def moll (d : ℕ) (ε : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, eta d ε (x - y) * u y

theorem moll_eq_cv (ε : ℝ) (u : Euc d → ℝ) : moll d ε u = cv u (eta d ε) := by
  funext x
  rw [cv_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

theorem moll_contDiff {ε : ℝ} (hε : 0 < ε) {u : Euc d → ℝ} (hu : LocallyIntegrable u volume) :
    ContDiff ℝ ∞ (moll d ε u) := by
  rw [moll_eq_cv]; exact contDiff_cv hu (eta_hasCompactSupport hε) eta_contDiff

theorem exists_eta_deriv_bound {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : Euc d, ‖iteratedFDeriv ℝ k (eta d ε) t‖ ≤ M := by
  have hc : Continuous (iteratedFDeriv ℝ k (eta d ε)) :=
    eta_contDiff.continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support ((eta_hasCompactSupport hε).iteratedFDeriv k)
  exact ⟨max M 0, le_max_right _ _, fun t => (hM t).trans (le_max_left _ _)⟩

/-- Every derivative of `z_ε` is bounded by `C_k(ε) B` (`C_k` depending only on `d, ε, k`). -/
theorem moll_iteratedFDeriv_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → LocMass B u → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ k (moll d ε u) x‖ ≤ C * B := by
  obtain ⟨M, hM0, hM⟩ := exists_eta_deriv_bound (d := d) hε k
  obtain ⟨K, hK0, hK⟩ := exists_closedBall_l1_real d ε
  refine ⟨M * K, by positivity, fun B u hB hu x => ?_⟩
  rw [moll_eq_cv]
  have := iteratedFDeriv_cv_le hu.locallyIntegrable (m := K * B) (hK B u hB hu) k ℝ (eta d ε)
    (eta_hasCompactSupport hε) eta_contDiff (eta_tsupport hε) M hM x
  rwa [mul_assoc]

/-! ### Fubini: `∫ z_ε ψ = ∫ u (η_ε * ψ)` -/

theorem integral_moll_mul {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, moll d ε u x * ψ x = ∫ y, u y * ∫ x, ψ x * eta d ε (x - y) := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Cψ, hCψ⟩ := hψ.bounded_above_of_compact_support hψc
  obtain ⟨Cη, hCη⟩ := (eta_contDiff (d := d) (ε := ε)).continuous.bounded_above_of_compact_support
    (eta_hasCompactSupport hε)
  set F : Euc d × Euc d → ℝ := fun p => ψ p.1 * (eta d ε (p.1 - p.2) * u p.2) with hF
  have hFi : Integrable F (volume.prod volume) := by
    set g : Euc d × Euc d → ℝ := fun p =>
      (closedBall (0 : Euc d) R).indicator (fun _ => Cψ * Cη) p.1 *
        (closedBall (0 : Euc d) (R + ε)).indicator (fun y => ‖u y‖) p.2 with hg
    have hg1 : Integrable ((closedBall (0 : Euc d) R).indicator fun _ => Cψ * Cη) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
    have hg2 : Integrable ((closedBall (0 : Euc d) (R + ε)).indicator fun y => ‖u y‖) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (hu.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall _ _)).norm
    have c1 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
    have c2 : 0 ≤ Cη := (norm_nonneg _).trans (hCη 0)
    have hg0 : ∀ p, 0 ≤ g p := fun p =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => mul_nonneg c1 c2) _)
        (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    refine (hg1.mul_prod hg2).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous fun p : Euc d × Euc d => ψ p.1 * eta d ε (p.1 - p.2) :=
        (hψ.comp continuous_fst).mul (eta_contDiff.continuous.comp (continuous_fst.sub continuous_snd))
      have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => u p.2) (volume.prod volume) :=
        hu.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have := h1.aestronglyMeasurable.mul h2
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp [hF, mul_assoc]
    · by_cases h1 : p.1 ∈ closedBall (0 : Euc d) R
      · by_cases h2 : p.2 ∈ closedBall (0 : Euc d) (R + ε)
        · simp only [hF, hg, Set.indicator_of_mem h1, Set.indicator_of_mem h2, norm_mul]
          have a1 := hCψ p.1
          have a2 := hCη (p.1 - p.2)
          calc ‖ψ p.1‖ * (‖eta d ε (p.1 - p.2)‖ * ‖u p.2‖) ≤ Cψ * (Cη * ‖u p.2‖) := by gcongr
            _ = _ := by ring
        · have : eta d ε (p.1 - p.2) = 0 := by
            by_contra hne
            apply h2
            have := eta_support hε (Function.mem_support.2 hne)
            rw [mem_ball_zero_iff] at this
            rw [mem_closedBall_zero_iff] at h1 ⊢
            calc ‖p.2‖ = ‖p.1 - (p.1 - p.2)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖p.1‖ + ‖p.1 - p.2‖ := norm_sub_le _ _
              _ ≤ R + ε := by linarith
          have h0 : F p = 0 := by simp [hF, this]
          rw [h0, norm_zero]; exact hg0 p
      · have : ψ p.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h1 (hR h))
        have h0 : F p = 0 := by simp [hF, this]
        rw [h0, norm_zero]; exact hg0 p
  have e1 : ∀ x, moll d ε u x * ψ x = ∫ y, F (x, y) := fun x => by
    simp only [hF]
    rw [integral_const_mul, mul_comm]; rfl
  have e2 : ∀ y, ∫ x, F (x, y) = u y * ∫ x, ψ x * eta d ε (x - y) := fun y => by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF]; ring
  simp_rw [e1]
  rw [integral_integral_swap hFi]
  exact integral_congr_ae (Eventually.of_forall e2)

/-- Evenness form: `∫ z_ε ψ = ∫ u (η_ε * ψ)` with `(η_ε * ψ)(y) = ∫ η_ε(y - x) ψ(x) dx`. -/
theorem integral_moll_mul' {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, moll d ε u x * ψ x = ∫ y, u y * ∫ x, eta d ε (y - x) * ψ x := by
  rw [integral_moll_mul hε hu hψ hψc]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← eta_neg ε (x - y), neg_sub, mul_comm]

/-! ### Jensen and the local mass bound -/

theorem LocMass.locallyIntegrable_sq {B : ℝ} {u : Euc d → ℝ} (h : LocMass B u) :
    LocallyIntegrable (fun y => u y ^ 2) volume := fun x => by
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_, ?_⟩
  · exact (h.1.pow 2).restrict
  · rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) ((h.2 x).trans_lt ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow]

theorem enorm_sq_eq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

theorem jensen_sq {w f : Euc d → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hw1 : Integrable w volume)
    (hint : ∫ y, w y = 1) (h2 : Integrable (fun y => w y * f y) volume)
    (h3 : Integrable (fun y => w y * f y ^ 2) volume) :
    (∫ y, w y * f y) ^ 2 ≤ ∫ y, w y * f y ^ 2 := by
  set a := ∫ y, w y * f y with ha
  have key : (fun y => w y * (f y - a) ^ 2) =
      fun y => (w y * f y ^ 2 - (2 * a) * (w y * f y)) + a ^ 2 * w y := by
    funext y; ring
  have h0 : 0 ≤ ∫ y, w y * (f y - a) ^ 2 :=
    integral_nonneg fun y => mul_nonneg (hw0 y) (sq_nonneg _)
  have i1 : Integrable (fun y => w y * f y ^ 2 - (2 * a) * (w y * f y)) volume :=
    h3.sub (h2.const_mul _)
  have e1 : ∫ y, ((w y * f y ^ 2 - (2 * a) * (w y * f y)) + a ^ 2 * w y) =
      (∫ y, (w y * f y ^ 2 - (2 * a) * (w y * f y))) + ∫ y, a ^ 2 * w y :=
    integral_add i1 (hw1.const_mul _)
  have e2 : ∫ y, (w y * f y ^ 2 - (2 * a) * (w y * f y)) =
      (∫ y, w y * f y ^ 2) - ∫ y, (2 * a) * (w y * f y) := integral_sub h3 (h2.const_mul _)
  rw [key, e1, e2, integral_const_mul, integral_const_mul, hint, ← ha] at h0
  nlinarith

/-- Pointwise Jensen: `z_ε(x)² ≤ ∫ η_ε(x - y) u(y)² dy`. -/
theorem moll_sq_le {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) (x : Euc d) :
    moll d ε u x ^ 2 ≤ ∫ y, eta d ε (x - y) * u y ^ 2 := by
  have hcs : HasCompactSupport (fun y => eta d ε (x - y)) :=
    (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x)
  have hco : Continuous fun y => eta d ε (x - y) :=
    eta_contDiff.continuous.comp (continuous_const.sub continuous_id)
  have hw1 : Integrable (fun y => eta d ε (x - y)) volume := hco.integrable_of_hasCompactSupport hcs
  have hint : ∫ y, eta d ε (x - y) = 1 := by
    rw [integral_sub_left_eq_self (fun y => eta d ε y) volume x, integral_eta hε]
  have h2 := hu.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hco hcs
  have h3 := hu.locallyIntegrable_sq.integrable_smul_left_of_hasCompactSupport hco hcs
  exact jensen_sq (fun y => eta_nonneg hε _) hw1 hint h2 h3

/-- The local mass bound: `∫_{ball c r} z_ε² ≤ ∫_{ball c (r+ε)} u²` (any `r`, any `ε > 0`). -/
theorem moll_mass_le {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) (c : Euc d)
    (r : ℝ) :
    ∫⁻ x in ball c r, ‖moll d ε u x‖ₑ ^ 2 ≤ ∫⁻ y in ball c (r + ε), ‖u y‖ₑ ^ 2 := by
  have hco : ∀ x : Euc d, Continuous fun y => eta d ε (x - y) := fun x =>
    eta_contDiff.continuous.comp (continuous_const.sub continuous_id)
  have hpt : ∀ x, ‖moll d ε u x‖ₑ ^ 2 ≤ ∫⁻ y, ENNReal.ofReal (eta d ε (x - y)) * ‖u y‖ₑ ^ 2 := by
    intro x
    have hcs : HasCompactSupport (fun y => eta d ε (x - y)) :=
      (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x)
    have h3 := hu.locallyIntegrable_sq.integrable_smul_left_of_hasCompactSupport (hco x) hcs
    have hnn : 0 ≤ᵐ[volume] fun y => eta d ε (x - y) * u y ^ 2 :=
      Eventually.of_forall fun y => mul_nonneg (eta_nonneg hε _) (sq_nonneg _)
    rw [enorm_sq_eq]
    calc ENNReal.ofReal (moll d ε u x ^ 2) ≤ ENNReal.ofReal (∫ y, eta d ε (x - y) * u y ^ 2) :=
          ENNReal.ofReal_le_ofReal (moll_sq_le hε hu x)
      _ = ∫⁻ y, ENNReal.ofReal (eta d ε (x - y) * u y ^ 2) := ofReal_integral_eq_lintegral_ofReal h3 hnn
      _ = _ := by
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (eta_nonneg hε _), enorm_sq_eq]
  have hmeas : AEMeasurable
      (Function.uncurry fun (x y : Euc d) => ENNReal.ofReal (eta d ε (x - y)) * ‖u y‖ₑ ^ 2)
      ((volume.restrict (ball c r)).prod volume) := by
    have h1 : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (eta d ε (p.1 - p.2)) :=
      ENNReal.measurable_ofReal.comp
        (eta_contDiff.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    have h2 : AEMeasurable (fun p : Euc d × Euc d => ‖u p.2‖ₑ ^ 2)
        ((volume.restrict (ball c r)).prod volume) :=
      (hu.1.enorm.pow_const 2).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact h1.aemeasurable.mul h2
  have hinner : ∀ y, (∫⁻ x in ball c r, ENNReal.ofReal (eta d ε (x - y)) * ‖u y‖ₑ ^ 2) ≤
      (ball c (r + ε)).indicator (fun y => ‖u y‖ₑ ^ 2) y := by
    intro y
    have hmx : Measurable fun x : Euc d => ENNReal.ofReal (eta d ε (x - y)) :=
      ENNReal.measurable_ofReal.comp
        (eta_contDiff.continuous.comp (continuous_id.sub continuous_const)).measurable
    rw [lintegral_mul_const _ hmx]
    by_cases hy : y ∈ ball c (r + ε)
    · rw [Set.indicator_of_mem hy]
      calc _ ≤ (∫⁻ x, ENNReal.ofReal (eta d ε (x - y))) * ‖u y‖ₑ ^ 2 :=
            mul_le_mul_left (setLIntegral_le_lintegral _ _) _
        _ = ‖u y‖ₑ ^ 2 := by
            have hi : Integrable (fun x => eta d ε (x - y)) volume :=
              (eta_contDiff.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
                ((eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subRight y))
            rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => eta_nonneg hε _),
              integral_sub_right_eq_self (fun x => eta d ε x) y, integral_eta hε]
            simp
    · rw [Set.indicator_of_notMem hy]
      have h0 : ∫⁻ x in ball c r, ENNReal.ofReal (eta d ε (x - y)) = ∫⁻ x in ball c r, 0 := by
        refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
        have : eta d ε (x - y) = 0 := by
          by_contra hne
          apply hy
          have h1 := eta_support hε (Function.mem_support.2 hne)
          rw [mem_ball_zero_iff] at h1
          rw [mem_ball] at hx ⊢
          have := dist_triangle y x c
          rw [dist_eq_norm y x] at this
          rw [norm_sub_rev] at h1
          linarith
        simp [this]
      rw [h0]; simp
  calc ∫⁻ x in ball c r, ‖moll d ε u x‖ₑ ^ 2
      ≤ ∫⁻ x in ball c r, ∫⁻ y, ENNReal.ofReal (eta d ε (x - y)) * ‖u y‖ₑ ^ 2 := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ x in ball c r, ENNReal.ofReal (eta d ε (x - y)) * ‖u y‖ₑ ^ 2 :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ y, (ball c (r + ε)).indicator (fun y => ‖u y‖ₑ ^ 2) y := lintegral_mono hinner
    _ = _ := lintegral_indicator measurableSet_ball _

/-! ### Packaged corollaries -/

/-- `ulocNormE m χ u ≤ ofReal B` for any `B : ℝ` (negative `B` allowed): `LocMass (max B 0) u`. -/
theorem locMass_of_ulocNormE' {m : ℕ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ}
    {B : ℝ} (hu : ulocNormE m χ u ≤ ENNReal.ofReal B) : LocMass (max B 0) u := by
  refine locMass_of_ulocNormE (m := m) hχ (le_max_right _ _) ?_
  have : ENNReal.ofReal (max B 0) = ENNReal.ofReal B := by
    rcases le_total B 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  rwa [this]

/-- Monotonicity in the radius (`r ≤ 1`). -/
theorem LocMass.ball_le {B : ℝ} {u : Euc d → ℝ} (h : LocMass B u) (c : Euc d) {r : ℝ} (hr : r ≤ 1) :
    ∫⁻ y in ball c r, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2) :=
  (lintegral_mono_set (ball_subset_ball hr)).trans (h.2 c)

/-- Uniform bound `∫_{ball c r} z_ε² ≤ N(d,r) B²` for all `0 < ε ≤ 1`. -/
theorem moll_mass_le_const (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ) (u : Euc d → ℝ), LocMass B u → ∀ c : Euc d,
      ∫⁻ x in ball c r, ‖moll d ε u x‖ₑ ^ 2 ≤ (N : ℝ≥0∞) * ENNReal.ofReal (B ^ 2) := by
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d (r + 1)
  refine ⟨N, fun ε hε hε1 B u hu c => ?_⟩
  exact (moll_mass_le hε hu c r).trans
    ((lintegral_mono_set (ball_subset_ball (by linarith))).trans (hN B u hu c))

end HRS.MS.UniqM1
