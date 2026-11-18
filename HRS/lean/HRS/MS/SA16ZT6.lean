import HRS.MS.SA16ZT5

/-!
# S.A.16 (SA16Z) T6: the sharp truncation versus the smooth one, and the principal value theorem

`sa16z_pv_tendsto`: `∫_{|z|>ε} K_i(z) f(x-z) dz → ∂_i (g ⋆ f)(x)`, `ε → 0+`, `f ∈ C_c^∞`, `0 ≤ s < d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T6
variable {d : ℕ} {s : ℝ}

/-- the difference of the sharp and the smooth cutoff -/
def sa16z_w (d : ℕ) (ε : ℝ) (z : Euc d) : ℝ := (if ε < ‖z‖ then 1 else 0) - sa16z_chi d ε z

lemma sa16z_w_neg (ε : ℝ) (z : Euc d) : sa16z_w d ε (-z) = sa16z_w d ε z := by
  simp [sa16z_w, sa16z_chi_neg, norm_neg]

lemma sa16z_w_near {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ‖z‖ ≤ ε) : sa16z_w d ε z = 0 := by
  simp [sa16z_w, sa16z_chi_zero hε hz, not_lt.2 hz]

lemma sa16z_w_far {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε ^ 2 ≤ ‖z‖ ^ 2) : sa16z_w d ε z = 0 := by
  have : ε < ‖z‖ := by
    by_contra h
    have h1 : ‖z‖ ≤ ε := not_lt.1 h
    have : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_pos_of_pos hε]
  simp [sa16z_w, sa16z_chi_one hε hz, this]

lemma sa16z_w_abs_le {ε : ℝ} (z : Euc d) : |sa16z_w d ε z| ≤ 1 := by
  unfold sa16z_w
  have h1 := sa16z_chi_nonneg ε z
  have h2 := sa16z_chi_le_one ε z
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma sa16z_w_meas (ε : ℝ) : Measurable (sa16z_w d ε) := by
  unfold sa16z_w
  exact (Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
    measurable_const).sub (sa16z_chi_smooth ε).continuous.measurable

lemma sa16z_w_supp {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε < ‖z‖) : sa16z_w d ε z = 0 :=
  sa16z_w_far hε (by nlinarith [norm_nonneg z])

lemma sa16z_wK_bdd (hs0 : 0 ≤ s) (i : Fin d) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    ‖sa16z_w d ε z * sa16z_Kx s i z‖ ≤ HRS.CZ.Hls.hlsg_c s * ε ^ (-s - 1) := by
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : ‖z‖ ≤ ε
  · rw [sa16z_w_near hε hz]; simp
    exact mul_nonneg (HRS.CZ.Hls.hlsg_c_nonneg hs0) (Real.rpow_nonneg hε.le _)
  · calc |sa16z_w d ε z| * |sa16z_Kx s i z| ≤ 1 * |sa16z_Kx s i z| :=
          mul_le_mul_of_nonneg_right (sa16z_w_abs_le z) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact sa16z_Kx_bound_far hs0 i hε (not_le.1 hz).le

lemma sa16z_wK_int (hs0 : 0 ≤ s) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z => sa16z_w d ε z * sa16z_Kx s i z) := by
  have hb : Integrable (indicator (closedBall (0 : Euc d) (2 * ε))
      (fun _ => HRS.CZ.Hls.hlsg_c s * ε ^ (-s - 1))) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top.ne))
  refine hb.mono' ((sa16z_w_meas ε).mul (sa16z_Kx_meas s i)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ≤ 2 * ε
  · rw [indicator_of_mem (by simpa using hz)]; exact sa16z_wK_bdd hs0 i hε z
  · rw [indicator_of_notMem (by simpa using hz), sa16z_w_supp hε (not_le.1 hz)]; simp

theorem sa16z_E_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ} (hF : IsCcInfty F)
    (i : Fin d) :
    Tendsto (fun ε : ℝ => ∫ z, sa16z_w d ε z * (sa16z_Kx s i z * F z)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hF.2 (hF.1.of_le (by simp)) (n := 1) one_ne_zero
  have hC0 : (0 : ℝ) ≤ C := C.2
  have hFl : ∀ z, |F z - F 0| ≤ C * ‖z‖ := by
    intro z
    have := hC.dist_le_mul z 0
    simpa [Real.dist_eq, dist_eq_norm] using this
  have hFint : Integrable F := hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hrw : ∀ ε : ℝ, 0 < ε → ∫ z, sa16z_w d ε z * (sa16z_Kx s i z * F z) =
      ∫ z, (sa16z_w d ε z * sa16z_Kx s i z) * (F z - F 0) := by
    intro ε hε
    have hint2 : Integrable (fun z => (sa16z_w d ε z * sa16z_Kx s i z) * F z) :=
      hFint.bdd_mul ((sa16z_w_meas ε).mul (sa16z_Kx_meas s i)).aestronglyMeasurable
        (Eventually.of_forall (sa16z_wK_bdd hs0 i hε)) |>.congr (Eventually.of_forall fun z => rfl)
    rw [← sa16z_odd_sub (h := fun z => sa16z_w d ε z * sa16z_Kx s i z) (F := F)
      (fun z => by simp only [sa16z_w_neg, sa16z_Kx_neg]; ring) (sa16z_wK_int hs0 i hε) hint2]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  have hint1 : IntegrableOn (fun z : Euc d => HRS.CZ.Hls.hlsg_c s * C * ‖z‖ ^ (-s)) (ball (0 : Euc d) 3) := by
    have := (HRS.S16Frac.s16frac_integrableOn_ball_rpow (d := d) hd (α := s) hsd 3).const_mul
      (HRS.CZ.Hls.hlsg_c s * C)
    exact this
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (l := 𝓝[>] (0 : ℝ))
    (F := fun (ε : ℝ) (z : Euc d) => (sa16z_w d ε z * sa16z_Kx s i z) * (F z - F 0))
    (f := fun _ => (0 : ℝ))
    (fun z => (indicator (ball (0 : Euc d) 3) (fun z => HRS.CZ.Hls.hlsg_c s * C * ‖z‖ ^ (-s))) z) ?_ ?_
    ((integrable_indicator_iff measurableSet_ball).2 hint1) ?_
  · have := key.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hrw ε hε).symm)
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (((sa16z_w_meas ε).mul (sa16z_Kx_meas s i)).mul
      ((hF.1.continuous.sub continuous_const).measurable)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    refine Eventually.of_forall fun z => ?_
    have hε0 : 0 < ε := hε.1
    have hc0 := HRS.CZ.Hls.hlsg_c_nonneg hs0
    by_cases hz : 2 * ε < ‖z‖
    · rw [sa16z_w_supp hε0 hz]
      simp
      exact indicator_nonneg (fun z _ => by positivity) z
    · have hz1 : ‖z‖ < 3 := by linarith [hε.2, not_lt.1 hz]
      rw [indicator_of_mem (by simpa using hz1)]
      by_cases hz0 : z = 0
      · subst hz0; simp
        exact mul_nonneg (mul_nonneg hc0 hC0) (Real.rpow_nonneg le_rfl _)
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have hK := sa16z_Kx_bound hs0 i hz0
        have h1 : |sa16z_w d ε z| ≤ 1 := sa16z_w_abs_le z
        have h2 : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
          rw [← Real.rpow_add_one hzpos.ne']; congr 1; ring
        calc |sa16z_w d ε z| * |sa16z_Kx s i z| * |F z - F 0|
            ≤ 1 * (HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1)) * (C * ‖z‖) := by
              gcongr
              · exact (hFl z)
          _ = HRS.CZ.Hls.hlsg_c s * C * (‖z‖ ^ (-s - 1) * ‖z‖) := by ring
          _ = _ := by rw [h2]
  · filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with z hz
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, (sa16z_w d ε z * sa16z_Kx s i z) * (F z - F 0) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖z‖ / 2 by
        have := norm_pos_iff.2 hz; linarith)] with ε hε
      have hlt : ε * ε < (‖z‖ / 2) * (‖z‖ / 2) := mul_self_lt_mul_self hε.1.le hε.2
      rw [sa16z_w_far hε.1 (by nlinarith [norm_nonneg z])]
      simp
    exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)

end T6

end HRS.Whole.AppendixA.Phase2SA16R
