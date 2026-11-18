import HRS.MS.UniqN1aB

/-!
# N1a of `UniqPlan.md`, part (c): the boundary (cutoff) term and the weak derivative

`n1a_cut_bound`: `|∫ k(y-x) F(x) ∂_j[Φ_ε(y-·)](x) dx| ≤ C ε^{d-a-1}`; `n1a_weak_deriv`:
`∫ k(y-x) ∂_jF(x) dx = ∫ (∂_jk)(y-x) F(x) dx`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0 HRS.MH.Screened

variable {d : ℕ}

theorem n1a_fderiv_shift (y : Euc d) (ε : ℝ) (x : Euc d) (v : Euc d) :
    fderiv ℝ (fun x => n1aΦ ε (y - x)) x v = -(fderiv ℝ (n1aΦ (d := d) ε) (y - x) v) := by
  have h1 : HasFDerivAt (fun x : Euc d => y - x) (0 - ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_const y x).sub (hasFDerivAt_id x)
  have h2 : HasFDerivAt (n1aΦ (d := d) ε) (fderiv ℝ (n1aΦ (d := d) ε) (y - x)) (y - x) :=
    (((n1aΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).differentiable
      one_ne_zero _).hasFDerivAt
  have h3 : HasFDerivAt (fun x => n1aΦ (d := d) ε (y - x)) _ x := h2.comp x h1
  rw [h3.fderiv]
  simp

theorem n1a_cut_bound {k : Euc d → ℝ} (j : Fin d) {a A M L : ℝ} (ha0 : 0 ≤ a)
    (hkb : ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |k z| ≤ A * ‖z‖ ^ (-a))
    {F : Euc d → ℝ} (hFb : ∀ x, |F x| ≤ M)
    (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) (y : Euc d) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ‖∫ x, k (y - x) * (F x * fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1))‖ ≤
      (max A 0 * M * L * 2 ^ d * (volume (closedBall (0 : Euc d) 1)).toReal) *
        ε ^ ((d : ℝ) - a - 1) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFb 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set c : ℝ := max A 0 * ε ^ (-a) * M * (L * ε⁻¹) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ x, ‖k (y - x) * (F x * fderiv ℝ (fun x => n1aΦ ε (y - x)) x
      (EuclideanSpace.single j 1))‖ ≤ (closedBall y (2 * ε)).indicator (fun _ => c) x := by
    intro x
    by_cases hx : x ∈ closedBall y (2 * ε)
    · rw [Set.indicator_of_mem hx]
      have hxn : ‖y - x‖ ≤ 2 * ε := by
        rw [← dist_eq_norm, dist_comm]; exact mem_closedBall.1 hx
      by_cases hin : ‖y - x‖ < ε
      · rw [n1a_fderiv_shift, n1aΦ_fderiv_zero_in hε hin]; simp [hc0]
      · have hin' : ε ≤ ‖y - x‖ := not_lt.1 hin
        have hz0 : y - x ≠ 0 := by
          intro h; rw [h, norm_zero] at hin'; linarith
        have hk1 := hkb (y - x) hz0 (by linarith)
        have hkp : ‖y - x‖ ^ (-a) ≤ ε ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hε hin' (by linarith)
        have hkk : |k (y - x)| ≤ max A 0 * ε ^ (-a) := by
          refine hk1.trans ?_
          exact mul_le_mul (le_max_left _ _) hkp (by positivity) (le_max_right _ _)
        have hD : |fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1)| ≤ L * ε⁻¹ := by
          rw [n1a_fderiv_shift, abs_neg, ← Real.norm_eq_abs]
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          have := n1aΦ_fderiv_bound hL hε (y - x)
          simpa using this
        rw [Real.norm_eq_abs, abs_mul, abs_mul, hc]
        have hDn := abs_nonneg (fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1))
        calc |k (y - x)| * (|F x| * |fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1)|)
            ≤ (max A 0 * ε ^ (-a)) * (M * (L * ε⁻¹)) :=
              mul_le_mul hkk (mul_le_mul (hFb x) hD hDn hM) (by positivity) (by positivity)
          _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      have hxn : 2 * ε < ‖y - x‖ := by
        by_contra h
        exact hx (mem_closedBall.2 (by rw [dist_comm, dist_eq_norm]; linarith [not_lt.1 h]))
      rw [n1a_fderiv_shift, n1aΦ_fderiv_zero_out hε hxn]; simp
  have hint : Integrable ((closedBall y (2 * ε)).indicator (fun _ : Euc d => c)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ measurableSet_closedBall]
  simp only [smul_eq_mul, Measure.real]
  have hvol : (volume (closedBall y (2 * ε))).toReal ≤
      (2 * ε) ^ (d : ℝ) * (volume (closedBall (0 : Euc d) 1)).toReal := by
    have h := l1_vol_closedBall_le y (le_refl (2 * ε)) (by linarith : 0 ≤ 2 * ε)
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hV1 : 0 ≤ (volume (closedBall (0 : Euc d) 1)).toReal := ENNReal.toReal_nonneg
  calc (volume (closedBall y (2 * ε))).toReal * c ≤
        ((2 * ε) ^ (d : ℝ) * (volume (closedBall (0 : Euc d) 1)).toReal) * c :=
        mul_le_mul_of_nonneg_right hvol hc0
    _ = (max A 0 * M * L * 2 ^ d * (volume (closedBall (0 : Euc d) 1)).toReal) *
        (ε ^ (-a) * ε⁻¹ * ε ^ (d : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) hε.le, hc, Real.rpow_natCast]
        ring
    _ = _ := by
        congr 1
        rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε]
        congr 1; ring

theorem n1a_phi_tendsto (y x : Euc d) (hxy : x ≠ y) :
    Tendsto (fun ε : ℝ => n1aΦ ε (y - x)) (𝓝[>] 0) (𝓝 1) := by
  have hn : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy.symm)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖y - x‖ / 2 by positivity)] with ε hε
  exact (n1aΦ_one hε.1 (by linarith [hε.2])).symm

theorem n1a_weak_deriv (hd : 1 ≤ d) {k : Euc d → ℝ} (j : Fin d)
    (hkd : ∀ z, z ≠ 0 → ContDiffAt ℝ 1 k z) (hk : LocallyIntegrable k volume)
    (hk' : LocallyIntegrable (fun z => fderiv ℝ k z (EuclideanSpace.single j 1)) volume)
    {a A : ℝ} (ha0 : 0 ≤ a) (had : a + 1 < d)
    (hkb : ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |k z| ≤ A * ‖z‖ ^ (-a))
    {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (y : Euc d) :
    ∫ x, k (y - x) * fderiv ℝ F x (EuclideanSpace.single j 1) =
      ∫ x, fderiv ℝ k (y - x) (EuclideanSpace.single j 1) * F x := by
  set v : Euc d := EuclideanSpace.single j (1 : ℝ) with hv
  obtain ⟨L, hL0, hL⟩ := n1a_bump_fderiv_bound (d := d)
  obtain ⟨M, hM⟩ := hF.continuous.bounded_above_of_compact_support hFc
  have hFb : ∀ x, |F x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x
  have hDc : Continuous (fun x => fderiv ℝ F x v) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun x => fderiv ℝ F x v) :=
    (hFc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have I1 : Integrable (fun x => k (y - x) * fderiv ℝ F x v) volume :=
    n1a_conv_integrable hk hDc hDcs y
  have I2 : Integrable (fun x => fderiv ℝ k (y - x) v * F x) volume :=
    n1a_conv_integrable hk' hF.continuous hFc y
  have hΦc : ∀ ε : ℝ, Continuous (fun x : Euc d => n1aΦ ε (y - x)) := fun ε =>
    ((n1aΦ_contDiff (d := d) ε).continuous).comp (continuous_const.sub continuous_id)
  have hΦ1 : ∀ ε : ℝ, ContDiff ℝ 1 (fun x : Euc d => n1aΦ ε (y - x)) := fun ε =>
    ((n1aΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).comp
      (contDiff_const.sub contDiff_id)
  have hDΦc : ∀ ε : ℝ, Continuous (fun x => fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v) :=
    fun ε => ((hΦ1 ε).continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- the three families
  have J1 : ∀ ε : ℝ, Integrable (fun x => k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v)) volume := by
    intro ε
    refine I1.norm.mono' ?_ (Eventually.of_forall fun x => ?_)
    · have := I1.aestronglyMeasurable.mul (hΦc ε).aestronglyMeasurable
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring
    · rw [Real.norm_eq_abs, show k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v) =
        (k (y - x) * fderiv ℝ F x v) * n1aΦ ε (y - x) by ring, abs_mul,
        abs_of_nonneg (n1aΦ_nonneg ε _), ← Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (n1aΦ_le_one ε _)
  have J2 : ∀ ε : ℝ, Integrable (fun x => fderiv ℝ k (y - x) v * (F x * n1aΦ ε (y - x))) volume := by
    intro ε
    refine I2.norm.mono' ?_ (Eventually.of_forall fun x => ?_)
    · have := I2.aestronglyMeasurable.mul (hΦc ε).aestronglyMeasurable
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring
    · rw [Real.norm_eq_abs, show fderiv ℝ k (y - x) v * (F x * n1aΦ ε (y - x)) =
        (fderiv ℝ k (y - x) v * F x) * n1aΦ ε (y - x) by ring, abs_mul,
        abs_of_nonneg (n1aΦ_nonneg ε _), ← Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (n1aΦ_le_one ε _)
  have J3 : ∀ ε : ℝ, Integrable (fun x => k (y - x) *
      (F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v)) volume := fun ε =>
    n1a_conv_integrable hk (h := fun x => F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v)
      (hF.continuous.mul (hDΦc ε)) (hFc.mul_right) y
  have hae := k3_ae_ne hd y
  -- limits
  have T1 : Tendsto (fun ε : ℝ => ∫ x, k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v))
      (𝓝[>] 0) (𝓝 (∫ x, k (y - x) * fderiv ℝ F x v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖k (y - x) * fderiv ℝ F x v‖)
      (Eventually.of_forall fun ε => (J1 ε).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_) I1.norm ?_
    · rw [Real.norm_eq_abs, show k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v) =
        (k (y - x) * fderiv ℝ F x v) * n1aΦ ε (y - x) by ring, abs_mul,
        abs_of_nonneg (n1aΦ_nonneg ε _), ← Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (n1aΦ_le_one ε _)
    · filter_upwards [hae] with x hx
      have := ((n1a_phi_tendsto y x hx).mul_const (fderiv ℝ F x v)).const_mul (k (y - x))
      simpa using this
  have T2 : Tendsto (fun ε : ℝ => ∫ x, fderiv ℝ k (y - x) v * (F x * n1aΦ ε (y - x)))
      (𝓝[>] 0) (𝓝 (∫ x, fderiv ℝ k (y - x) v * F x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖fderiv ℝ k (y - x) v * F x‖)
      (Eventually.of_forall fun ε => (J2 ε).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_) I2.norm ?_
    · rw [Real.norm_eq_abs, show fderiv ℝ k (y - x) v * (F x * n1aΦ ε (y - x)) =
        (fderiv ℝ k (y - x) v * F x) * n1aΦ ε (y - x) by ring, abs_mul,
        abs_of_nonneg (n1aΦ_nonneg ε _), ← Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (n1aΦ_le_one ε _)
    · filter_upwards [hae] with x hx
      have := ((n1a_phi_tendsto y x hx).const_mul (F x)).const_mul (fderiv ℝ k (y - x) v)
      simpa using this
  have T3 : Tendsto (fun ε : ℝ => ∫ x, k (y - x) *
      (F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v)) (𝓝[>] 0) (𝓝 0) := by
    have he : 0 < (d : ℝ) - a - 1 := by linarith
    have hrp : Tendsto (fun ε : ℝ => ε ^ ((d : ℝ) - a - 1)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) ((d : ℝ) - a - 1) (Or.inr he.le)).tendsto
      rw [Real.zero_rpow he.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    set C : ℝ := max A 0 * M * L * 2 ^ d * (volume (closedBall (0 : Euc d) 1)).toReal with hC
    have hrp2 : Tendsto (fun ε : ℝ => C * ε ^ ((d : ℝ) - a - 1)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hrp.const_mul C
    refine squeeze_zero_norm' ?_ hrp2
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact n1a_cut_bound j ha0 hkb hFb hL y hε.1 hε.2.le
  -- the identity
  have hid : ∀ ε : ℝ, 0 < ε → (∫ x, k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v)) =
      (∫ x, fderiv ℝ k (y - x) v * (F x * n1aΦ ε (y - x))) -
        ∫ x, k (y - x) * (F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v) := by
    intro ε hε
    have h := n1a_ibp_eps j hkd hF hFc y hε
    have e : ∀ x, k (y - x) * (F x * fderiv ℝ (fun x => n1aΦ ε (y - x)) x v +
        n1aΦ ε (y - x) * fderiv ℝ F x v) =
        k (y - x) * (F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v) +
          k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v) := fun x => by ring
    rw [← hv] at h
    simp only [e] at h
    rw [integral_add (J3 ε) (J1 ε)] at h
    linarith
  have T4 : Tendsto (fun ε : ℝ => ∫ x, k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v))
      (𝓝[>] 0) (𝓝 ((∫ x, fderiv ℝ k (y - x) v * F x) - 0)) := by
    refine (T2.sub T3).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hid ε hε).symm
  have := tendsto_nhds_unique T1 T4
  rw [this, sub_zero]

end HRS.MS.UniqN1a
