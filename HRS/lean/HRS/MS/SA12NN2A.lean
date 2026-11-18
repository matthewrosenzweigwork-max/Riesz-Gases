import HRS.MS.UniqN1aF
import HRS.MS.SA12Z3NearN5A

/-!
# S.A.12 N2 (SA12N), part A: the weak derivative with a vanishing test function

`sa12n_weak_deriv`: `∫ k(y-x) ∂_jF(x) dx = ∫ (∂_j k)(y-x) F(x) dx` for `F ∈ C¹_c` with `|F(x)| ≤ M ‖y-x‖^p`
(`p ≥ 0`), `k` smooth off `0`, locally integrable, `|k(z)| ≤ A ‖z‖^{-a}` near `0` with `a + 1 < d + p`;
the derivative `∂_j k` is only required to make `∂_j k(y-·) F` integrable (a hypothesis).  This is
`UniqN1a.n1a_weak_deriv` with the boundary term of the cutoff `Φ_ε` estimated by `ε^{d-a-1+p}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0 HRS.MH.Screened
  HRS.MS.UniqN1a

variable {d : ℕ}

theorem sa12n_cut_bound {k : Euc d → ℝ} (j : Fin d) {a A M L p : ℝ} (ha0 : 0 ≤ a) (hp : 0 ≤ p)
    (hM : 0 ≤ M)
    (hkb : ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |k z| ≤ A * ‖z‖ ^ (-a))
    {F : Euc d → ℝ} (y : Euc d) (hFb : ∀ x, |F x| ≤ M * ‖y - x‖ ^ p)
    (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ‖∫ x, k (y - x) * (F x * fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1))‖ ≤
      (max A 0 * M * L * 2 ^ (d : ℝ) * 2 ^ p * (volume (closedBall (0 : Euc d) 1)).toReal) *
        ε ^ ((d : ℝ) - a - 1 + p) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set c : ℝ := max A 0 * ε ^ (-a) * (M * (2 * ε) ^ p) * (L * ε⁻¹) with hc
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
        have hFx : |F x| ≤ M * (2 * ε) ^ p :=
          (hFb x).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hxn hp) hM)
        calc |k (y - x)| * (|F x| * |fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1)|)
            ≤ (max A 0 * ε ^ (-a)) * ((M * (2 * ε) ^ p) * (L * ε⁻¹)) :=
              mul_le_mul hkk (mul_le_mul hFx hD hDn (by positivity)) (by positivity) (by positivity)
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
    _ = (max A 0 * M * L * 2 ^ (d : ℝ) * 2 ^ p * (volume (closedBall (0 : Euc d) 1)).toReal) *
        (ε ^ (-a) * ε⁻¹ * ε ^ p * ε ^ (d : ℝ)) := by
        simp only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le, hc]
        ring
    _ = _ := by
        congr 1
        rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε, ← Real.rpow_add hε]
        congr 1; ring

/-- `k(y-·) G` is integrable if `G` is continuous with compact support away from `y`. -/
theorem sa12n_integrable_away {k G : Euc d → ℝ} (y : Euc d) {ε : ℝ} (hε : 0 < ε)
    (hkd : ∀ z, z ≠ 0 → ContDiffAt ℝ 1 k z) (hG : Continuous G) (hGc : HasCompactSupport G)
    (hGs : ∀ x, G x ≠ 0 → ε ≤ ‖y - x‖) : Integrable (fun x => k (y - x) * G x) volume := by
  have hcont : Continuous (fun x => k (y - x) * G x) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hxy : x = y
    · subst hxy
      have hev : (fun x' => k (x - x') * G x') =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds x hε] with x' hx'
        have : G x' = 0 := by
          by_contra hne
          have := hGs x' hne
          rw [mem_ball, dist_eq_norm, norm_sub_rev] at hx'
          linarith
        simp [this]
      exact continuousAt_const.congr hev.symm
    · have h1 : ContinuousAt (fun x' => k (y - x')) x :=
        ((hkd _ (sub_ne_zero.2 (Ne.symm hxy))).continuousAt).comp
          (f := fun x' => y - x') (continuous_const.sub continuous_id).continuousAt
      exact h1.mul hG.continuousAt
  exact hcont.integrable_of_hasCompactSupport hGc.mul_left

theorem sa12n_weak_deriv (hd : 1 ≤ d) {k : Euc d → ℝ} (j : Fin d)
    (hkd : ∀ z, z ≠ 0 → ContDiffAt ℝ 1 k z)
    {a A M p : ℝ} (ha0 : 0 ≤ a) (hp : 0 ≤ p) (hM0 : 0 ≤ M) (had : a + 1 < d + p)
    (hkb : ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |k z| ≤ A * ‖z‖ ^ (-a))
    {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (y : Euc d)
    (hFb : ∀ x, |F x| ≤ M * ‖y - x‖ ^ p)
    (hI1 : Integrable (fun x => k (y - x) * fderiv ℝ F x (EuclideanSpace.single j 1)) volume)
    (hI2 : Integrable (fun x => fderiv ℝ k (y - x) (EuclideanSpace.single j 1) * F x) volume) :
    ∫ x, k (y - x) * fderiv ℝ F x (EuclideanSpace.single j 1) =
      ∫ x, fderiv ℝ k (y - x) (EuclideanSpace.single j 1) * F x := by
  set v : Euc d := EuclideanSpace.single j (1 : ℝ) with hv
  obtain ⟨L, hL0, hL⟩ := n1a_bump_fderiv_bound (d := d)
  have hDc : Continuous (fun x => fderiv ℝ F x v) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun x => fderiv ℝ F x v) :=
    (hFc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L v) (by simp)
  have I1 : Integrable (fun x => k (y - x) * fderiv ℝ F x v) volume := hI1
  have I2 : Integrable (fun x => fderiv ℝ k (y - x) v * F x) volume := hI2
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
  have J3 : ∀ ε : ℝ, 0 < ε → Integrable (fun x => k (y - x) *
      (F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v)) volume := fun ε hε =>
    sa12n_integrable_away y hε hkd (G := fun x => F x * fderiv ℝ (fun x : Euc d => n1aΦ ε (y - x)) x v)
      (hF.continuous.mul (hDΦc ε)) (hFc.mul_right) (fun x hx => by
        by_contra hlt
        have hlt' : ‖y - x‖ < ε := not_le.1 hlt
        apply hx
        rw [n1a_fderiv_shift, n1aΦ_fderiv_zero_in hε hlt']
        simp)
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
    have he : 0 < (d : ℝ) - a - 1 + p := by linarith
    have hrp : Tendsto (fun ε : ℝ => ε ^ ((d : ℝ) - a - 1 + p)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) ((d : ℝ) - a - 1 + p) (Or.inr he.le)).tendsto
      rw [Real.zero_rpow he.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    set C : ℝ := max A 0 * M * L * 2 ^ (d : ℝ) * 2 ^ p * (volume (closedBall (0 : Euc d) 1)).toReal
      with hC
    have hrp2 : Tendsto (fun ε : ℝ => C * ε ^ ((d : ℝ) - a - 1 + p)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hrp.const_mul C
    refine squeeze_zero_norm' ?_ hrp2
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact sa12n_cut_bound j ha0 hp hM0 hkb y hFb hL hε.1 hε.2.le
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
    rw [integral_add (J3 ε hε) (J1 ε)] at h
    linarith
  have T4 : Tendsto (fun ε : ℝ => ∫ x, k (y - x) * (n1aΦ ε (y - x) * fderiv ℝ F x v))
      (𝓝[>] 0) (𝓝 ((∫ x, fderiv ℝ k (y - x) v * F x) - 0)) := by
    refine (T2.sub T3).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hid ε hε).symm
  have := tendsto_nhds_unique T1 T4
  rw [this, sub_zero]

end HRS.MH.AdjointRd.Phase2SA12Near
