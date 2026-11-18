import HRS.MS.UniqN2aA

/-!
# N2a of `UniqPlan.md`, part (b): the principal value of `∂_i g * ψ` at a fixed point

For `d - 1 < s < d`, `ψ ∈ C¹_c` and `y ∈ ℝ^d` put
`A_ε(y) := ∫ 1_{ε<‖z‖} κ(z) ψ(y-z) dz` (`κ = ∂_i g`).  We prove

* `pv_tendsto`: `A_ε(y) → kernelConvDeriv d s i ψ y` as `ε → 0⁺` (integration by parts through the
  regularisation `G_δ` and the subtraction of `ψ(y)`, which is allowed since `κ` is odd);
* `pv_bound`: `|A_ε(y)| ≤ C₀` with `C₀` independent of `ε > 0` and `y`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1
  HRS.MS.UniqT3

variable {d : ℕ}

/-- Lipschitz and sup bounds of a `C¹_c` function. -/
theorem psi_bounds {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ (∀ x y, |ψ x - ψ y| ≤ L * ‖x - y‖) ∧ ∀ x, |ψ x| ≤ B := by
  obtain ⟨C, hC⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc one_ne_zero
  obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  refine ⟨C, max B 0, C.2, le_max_right _ _, fun x y => ?_, fun x => ?_⟩
  · have := hC.dist_le_mul x y
    simpa [Real.dist_eq, dist_eq_norm] using this
  · have h := hB x
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)

/-- The pointwise bound of the integrands. -/
theorem kernel_diff_bound {s K0 L B : ℝ} (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB : 0 ≤ B)
    {k : Euc d → ℝ} (hk : ∀ z : Euc d, z ≠ 0 → |k z| ≤ K0 * ‖z‖ ^ (-s - 1))
    {ψ : Euc d → ℝ} (hψL : ∀ x y, |ψ x - ψ y| ≤ L * ‖x - y‖) (hψB : ∀ x, |ψ x| ≤ B)
    (y : Euc d) {z : Euc d} (hz : z ≠ 0) :
    |k z * (ψ (y - z) - ψ y)| ≤ K0 * max L (2 * B) * Wf s z := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hΔ1 : |ψ (y - z) - ψ y| ≤ L * ‖z‖ := by
    have := hψL (y - z) y
    simpa using this
  have hΔ2 : |ψ (y - z) - ψ y| ≤ 2 * B := by
    calc |ψ (y - z) - ψ y| ≤ |ψ (y - z)| + |ψ y| := abs_sub _ _
      _ ≤ B + B := add_le_add (hψB _) (hψB _)
      _ = 2 * B := by ring
  have hkz := hk z hz
  rw [abs_mul]
  have hM : 0 ≤ max L (2 * B) := le_trans hL (le_max_left _ _)
  unfold Wf
  by_cases h1 : ‖z‖ < 1
  · have ht : tailF s z = 0 := by unfold tailF; simp [not_le.2 h1]
    have hb : ballF s z = ‖z‖ ^ (-s) := by unfold ballF; simp [h1]
    rw [ht, hb, add_zero]
    have h2 : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
      rw [← Real.rpow_add_one hzp.ne']; congr 1; ring
    calc |k z| * |ψ (y - z) - ψ y| ≤ (K0 * ‖z‖ ^ (-s - 1)) * (L * ‖z‖) :=
          mul_le_mul hkz hΔ1 (abs_nonneg _) (by positivity)
      _ = K0 * L * (‖z‖ ^ (-s - 1) * ‖z‖) := by ring
      _ = K0 * L * ‖z‖ ^ (-s) := by rw [h2]
      _ ≤ K0 * max L (2 * B) * ‖z‖ ^ (-s) := by
          gcongr; exact le_max_left _ _
  · have h1' : 1 ≤ ‖z‖ := not_lt.1 h1
    have ha : ballF s z = 0 := by unfold ballF; simp [h1]
    have hb : tailF s z = ‖z‖ ^ (-(s + 1)) := by unfold tailF; simp [h1']
    rw [ha, hb, zero_add]
    have h2 : (-s - 1) = -(s + 1) := by ring
    calc |k z| * |ψ (y - z) - ψ y| ≤ (K0 * ‖z‖ ^ (-s - 1)) * (2 * B) :=
          mul_le_mul hkz hΔ2 (abs_nonneg _) (by positivity)
      _ = K0 * (2 * B) * ‖z‖ ^ (-(s + 1)) := by rw [h2]; ring
      _ ≤ K0 * max L (2 * B) * ‖z‖ ^ (-(s + 1)) := by
          gcongr; exact le_max_right _ _

theorem DG_abs_le {s : ℝ} (hs0 : 0 < s) (δ : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |DG s δ i z| ≤ s * ‖z‖ ^ (-s - 1) := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have habs : |DG s δ i z| = s * |z i| * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) := by
    unfold DG
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hs0, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  rw [habs]
  have h2 : (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg δ]) (by linarith)
  have h5 : (‖z‖ ^ 2) ^ (-s / 2 - 1) = ‖z‖ ^ (-s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]; congr 1; push_cast; ring
  have h6 : ‖z‖ * ‖z‖ ^ (-s - 2) = ‖z‖ ^ (-s - 1) := by
    rw [← Real.rpow_one_add' hzp.le (by linarith)]; congr 1; ring
  have h4 : 0 ≤ (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) := by positivity
  calc s * |z i| * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1) ≤ s * ‖z‖ * ‖z‖ ^ (-s - 2) := by
        rw [← h5]; gcongr; exact n0_coord_le z i
    _ = s * ‖z‖ ^ (-s - 1) := by rw [mul_assoc, h6]

theorem ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
  filter_upwards [this] with z hz
  simpa using hz

theorem dpos {s : ℝ} (hs0 : 0 < s) (hsd : s < d) : 1 ≤ d := by
  have : (0 : ℝ) < d := hs0.trans hsd
  exact_mod_cast this

theorem G_tendsto (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun δ : ℝ => G s δ z) (𝓝[>] (0 : ℝ)) (𝓝 (‖z‖ ^ (-s))) := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc : Continuous (fun δ : ℝ => (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2)) :=
    (continuous_const.add (continuous_id.pow 2)).rpow_const (fun δ => Or.inl (show ‖z‖ ^ 2 + δ ^ 2 ≠ 0 from
        ne_of_gt (by nlinarith [sq_nonneg δ, pow_pos hzp 2])))
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have e : (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-s / 2) = ‖z‖ ^ (-s) := by
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul hzp.le]
    congr 1; push_cast; ring
  rw [e] at h
  exact h

theorem DG_tendsto {s : ℝ} (hs0 : 0 < s) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun δ : ℝ => DG s δ i z) (𝓝[>] (0 : ℝ)) (𝓝 (kap d s i z)) := by
  have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc : Continuous (fun δ : ℝ => -s * z i * (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2 - 1)) :=
    continuous_const.mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const (fun δ => Or.inl (show ‖z‖ ^ 2 + δ ^ 2 ≠ 0 from
        ne_of_gt (by nlinarith [sq_nonneg δ, pow_pos hzp 2]))))
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have e : -s * z i * (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-s / 2 - 1) = kap d s i z := by
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul hzp.le]
    have : ((2 : ℕ) : ℝ) * (-s / 2 - 1) = -s - 2 := by push_cast; ring
    rw [this]
    simp only [kap]
    rw [n0_gradRK s i hz]
    unfold q09_H q09_c
    simp [hs0.ne']
    ring
  rw [e] at h
  exact h

/-- Limit of the regularised convolution with `g`. -/
theorem G_conv_tendsto {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) :
    Tendsto (fun δ : ℝ => ∫ z, G s δ z * fderiv ℝ ψ (y - z) (EuclideanSpace.single i (1 : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (kernelConvDeriv d s i ψ y)) := by
  set a : Euc d → ℝ := fun z => fderiv ℝ ψ (y - z) (EuclideanSpace.single i (1 : ℝ)) with ha
  have hd1 : 1 ≤ d := dpos hs0 hsd
  have hac : Continuous a :=
    ((hψ.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const
  have hacs : HasCompactSupport a := by
    have h0 := D1_supp hψc i
    have := h0.comp_homeomorph (Homeomorph.subLeft y)
    exact this
  have hint : Integrable (fun z => rieszKernel d s z * a z) := by
    simpa using (rieszKernel_locallyIntegrable (d := d) hs0.le hsd).integrable_smul_right_of_hasCompactSupport
      hac hacs
  have heq : kernelConvDeriv d s i ψ y = ∫ z, rieszKernel d s z * a z := by
    unfold kernelConvDeriv
    rw [← integral_sub_left_eq_self (fun z => rieszKernel d s z * a z) volume y]
    simp [ha, sub_sub_cancel]
  rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun z => |rieszKernel d s z * a z|)
    ?_ ?_ hint.abs ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((G_continuous s (ne_of_gt hδ)).mul hac).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_ne_zero hd1] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hδ' : δ ≠ 0 := ne_of_gt hδ
    rw [Real.norm_eq_abs, rieszKernel_of_ne hs0.ne', abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖z‖ ^ (-s))]
    have hG0 : 0 ≤ G s δ z := by unfold G; positivity
    rw [abs_of_nonneg hG0]
    have : G s δ z ≤ ‖z‖ ^ (-s) := by
      unfold G
      calc (‖z‖ ^ 2 + δ ^ 2) ^ (-s / 2) ≤ (‖z‖ ^ 2) ^ (-s / 2) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg δ]) (by linarith)
        _ = ‖z‖ ^ (-s) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hzp.le]; congr 1; push_cast; ring
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · filter_upwards [ae_ne_zero hd1] with z hz
    rw [rieszKernel_of_ne hs0.ne']
    exact (G_tendsto s hz).mul_const _

/-- Limit of the regularised kernel `∂_iG_δ` against `ψ(y-z) - ψ(y)`. -/
theorem DG_diff_tendsto {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) :
    Tendsto (fun δ : ℝ => ∫ z, DG s δ i z * (ψ (y - z) - ψ y)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, kap d s i z * (ψ (y - z) - ψ y))) := by
  have hd1 : 1 ≤ d := dpos hs0 hsd
  obtain ⟨L, B, hL, hB, hψL, hψB⟩ := psi_bounds hψ hψc
  have hψm : Continuous (fun z => ψ (y - z) - ψ y) :=
    (hψ.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => K0 * max L (2 * B) * Wf s z) ?_ ?_
    ((Wf_integrable hs0 hsd hs1).const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((DG_continuous s (ne_of_gt hδ) i).mul hψm).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_ne_zero hd1] with z hz
    rw [Real.norm_eq_abs]
    refine kernel_diff_bound (s := s) hK00 hL hB (k := DG s δ i) (fun z hz => ?_) hψL hψB y hz
    exact (DG_abs_le hs0 δ i hz).trans (by gcongr; exact le_max_right _ _)
  · filter_upwards [ae_ne_zero hd1] with z hz
    exact (DG_tendsto hs0 i hz).mul_const _

/-- The identity `(g * ∂_iψ)(y) = ∫ κ(z) (ψ(y-z) - ψ(y)) dz`. -/
theorem kcd_eq_pv_diff {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) :
    kernelConvDeriv d s i ψ y = ∫ z, kap d s i z * (ψ (y - z) - ψ y) := by
  have h1 := G_conv_tendsto hs0 hsd i hψ hψc y
  have h2 := DG_diff_tendsto hs0 hsd hs1 i hψ hψc y
  have hF : Continuous (fun z => ψ (y - z)) := hψ.continuous.comp (continuous_const.sub continuous_id)
  have hFc : HasCompactSupport (fun z => ψ (y - z)) := hψc.comp_homeomorph (Homeomorph.subLeft y)
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ z, G s δ z * fderiv ℝ ψ (y - z) (EuclideanSpace.single i (1 : ℝ))) =
        ∫ z, DG s δ i z * (ψ (y - z) - ψ y) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : δ ≠ 0 := ne_of_gt hδ
    rw [← ibp_G s hδ' i hψ hψc y]
    have hi1 : Integrable (fun z => DG s δ i z * ψ (y - z)) :=
      ((DG_continuous s hδ' i).mul hF).integrable_of_hasCompactSupport (hFc.mul_left)
    have hi2 : Integrable (fun z => DG s δ i z * ψ y) :=
      (DG_integrable hs0 hs1 hδ' i).mul_const _
    simp_rw [mul_sub]
    rw [integral_sub hi1 hi2, integral_mul_const, DG_integral_zero, zero_mul, sub_zero]
  exact tendsto_nhds_unique (h1.congr' heq) h2

/-! ### The truncated integrals -/

theorem kap_trunc_integrable {s : ℝ} (hs0 : 0 < s) (hs1 : (d : ℝ) < s + 1) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) : Integrable (fun z : Euc d => if ε < ‖z‖ then kap d s i z else 0) := by
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  have hi := (((ind_ball_integrable (d := d)).const_mul (K0 * ε ^ (-s - 1))).add
    ((tailF_integrable hs1).const_mul K0))
  refine hi.mono' ((kap_measurable s i).ite (measurableSet_lt measurable_const measurable_norm)
    measurable_const).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  by_cases hz : ε < ‖z‖
  · rw [if_pos hz, Real.norm_eq_abs]
    have hzp : 0 < ‖z‖ := hε.trans hz
    have hk := kap_bound hs0.le i (norm_pos_iff.1 hzp)
    by_cases h1 : ‖z‖ < 1
    · have hb : z ∈ ball (0 : Euc d) 1 := by simpa using h1
      rw [Set.indicator_of_mem hb]
      have ht : tailF s z = 0 := by unfold tailF; simp [not_le.2 h1]
      rw [ht, mul_zero, add_zero]
      have : ‖z‖ ^ (-s - 1) ≤ ε ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos hε hz.le (by linarith)
      calc |kap d s i z| ≤ K0 * ‖z‖ ^ (-s - 1) := hk
        _ ≤ K0 * ε ^ (-s - 1) := by gcongr
        _ = _ := by ring
    · have hb : z ∉ ball (0 : Euc d) 1 := by simpa using h1
      rw [Set.indicator_of_notMem hb]
      have ht : tailF s z = ‖z‖ ^ (-(s + 1)) := by unfold tailF; simp [not_lt.1 h1]
      rw [ht, mul_zero, zero_add]
      have : (-s - 1) = -(s + 1) := by ring
      rw [← this]
      exact hk
  · rw [if_neg hz]
    simp only [norm_zero]
    have := tailF_nonneg s z
    have : 0 ≤ (ball (0 : Euc d) 1).indicator (fun _ => (1 : ℝ)) z :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    positivity

/-- Removing `ψ(y)` from the truncated integral (oddness of `κ`). -/
theorem pv_trunc_eq {s : ℝ} (hs0 : 0 < s) (hs1 : (d : ℝ) < s + 1) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, (if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0) =
      ∫ z, (if ε < ‖z‖ then kap d s i z * (ψ (y - z) - ψ y) else 0) := by
  have hF : Continuous (fun z => ψ (y - z)) := hψ.continuous.comp (continuous_const.sub continuous_id)
  have hFc : HasCompactSupport (fun z => ψ (y - z)) := hψc.comp_homeomorph (Homeomorph.subLeft y)
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  have hi2 := kap_trunc_integrable hs0 hs1 i hε
  have hi1 : Integrable (fun z : Euc d => if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0) := by
    have hint := hF.integrable_of_hasCompactSupport (μ := volume) hFc
    refine (hint.norm.const_mul (K0 * ε ^ (-s - 1))).mono'
      ((((kap_measurable s i).mul (hF.measurable)).ite
        (measurableSet_lt measurable_const measurable_norm) measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    by_cases hz : ε < ‖z‖
    · rw [if_pos hz, Real.norm_eq_abs, abs_mul]
      have hzp : 0 < ‖z‖ := hε.trans hz
      have hk := kap_bound hs0.le i (norm_pos_iff.1 hzp)
      have : ‖z‖ ^ (-s - 1) ≤ ε ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos hε hz.le (by linarith)
      calc |kap d s i z| * |ψ (y - z)| ≤ (K0 * ε ^ (-s - 1)) * |ψ (y - z)| := by
            gcongr
            exact hk.trans (by gcongr)
        _ = _ := by rw [Real.norm_eq_abs]
    · rw [if_neg hz]; simp only [norm_zero]
      positivity
  have hodd : ∫ z : Euc d, (if ε < ‖z‖ then kap d s i z else 0) = 0 := by
    have h : ∫ z : Euc d, (if ε < ‖-z‖ then kap d s i (-z) else 0) =
        ∫ z : Euc d, (if ε < ‖z‖ then kap d s i z else 0) :=
      integral_neg_eq_self (fun z : Euc d => if ε < ‖z‖ then kap d s i z else 0) volume
    simp only [norm_neg, kap_neg] at h
    have h2 : ∀ z : Euc d, (if ε < ‖z‖ then -kap d s i z else 0) =
        -(if ε < ‖z‖ then kap d s i z else 0) := fun z => by split_ifs <;> simp
    simp only [h2, integral_neg] at h
    linarith
  have hsplit : ∀ z : Euc d, (if ε < ‖z‖ then kap d s i z * (ψ (y - z) - ψ y) else 0) =
      (if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0) -
        (if ε < ‖z‖ then kap d s i z else 0) * ψ y := fun z => by
    split_ifs <;> ring
  simp only [hsplit]
  rw [integral_sub hi1 (hi2.mul_const _), integral_mul_const, hodd, zero_mul, sub_zero]

/-- Uniform bound on the truncated principal value. -/
theorem pv_bound {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ C0 : ℝ, ∀ (y : Euc d) {ε : ℝ}, 0 < ε →
      |∫ z, (if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0)| ≤ C0 := by
  obtain ⟨L, B, hL, hB, hψL, hψB⟩ := psi_bounds hψ hψc
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  refine ⟨K0 * max L (2 * B) * ∫ z, Wf (d := d) s z, fun y ε hε => ?_⟩
  rw [pv_trunc_eq hs0 hs1 i hψ hψc y hε]
  have hW := Wf_integrable hs0 hsd hs1
  have hle := norm_integral_le_of_norm_le (hW.const_mul (K0 * max L (2 * B)))
    (f := fun z : Euc d => (if ε < ‖z‖ then kap d s i z * (ψ (y - z) - ψ y) else 0))
    (Eventually.of_forall fun z => ?_)
  · rw [integral_const_mul] at hle
    simpa [Real.norm_eq_abs] using hle
  · by_cases hz : ε < ‖z‖
    · rw [if_pos hz, Real.norm_eq_abs]
      have hz0 : z ≠ 0 := norm_pos_iff.1 (hε.trans hz)
      exact kernel_diff_bound (s := s) hK00 hL hB (k := kap d s i) (fun z hz => kap_bound hs0.le i hz)
        hψL hψB y hz0
    · rw [if_neg hz]; simp only [norm_zero]
      have := Wf_nonneg (d := d) s z
      positivity

/-- Principal value: the truncated integrals converge to `kernelConvDeriv`. -/
theorem pv_tendsto {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (y : Euc d) :
    Tendsto (fun ε : ℝ => ∫ z, (if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0)) (𝓝[>] (0 : ℝ))
      (𝓝 (kernelConvDeriv d s i ψ y)) := by
  have hd1 : 1 ≤ d := dpos hs0 hsd
  obtain ⟨L, B, hL, hB, hψL, hψB⟩ := psi_bounds hψ hψc
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  have hF : Continuous (fun z => ψ (y - z)) := hψ.continuous.comp (continuous_const.sub continuous_id)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ z, (if ε < ‖z‖ then kap d s i z * ψ (y - z) else 0)) =
      ∫ z, (if ε < ‖z‖ then kap d s i z * (ψ (y - z) - ψ y) else 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pv_trunc_eq hs0 hs1 i hψ hψc y hε
  rw [kcd_eq_pv_diff hs0 hsd hs1 i hψ hψc y]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => K0 * max L (2 * B) * Wf s z) ?_ ?_
    ((Wf_integrable hs0 hsd hs1).const_mul _) ?_
  · exact Eventually.of_forall fun ε =>
      (((kap_measurable s i).mul ((hF.sub continuous_const).measurable)).ite
        (measurableSet_lt measurable_const measurable_norm) measurable_const).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun z => ?_
    by_cases hz : ε < ‖z‖
    · rw [if_pos hz, Real.norm_eq_abs]
      have hz0 : z ≠ 0 := norm_pos_iff.1 ((show (0:ℝ) < ε from hε).trans hz)
      exact kernel_diff_bound (s := s) hK00 hL hB (k := kap d s i) (fun z hz => kap_bound hs0.le i hz)
        hψL hψB y hz0
    · rw [if_neg hz]; simp only [norm_zero]
      have := Wf_nonneg (d := d) s z
      positivity
  · filter_upwards [ae_ne_zero hd1] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ‖z‖ := nhdsWithin_le_nhds (Iio_mem_nhds hzp)
    refine (tendsto_const_nhds (x := kap d s i z * (ψ (y - z) - ψ y))).congr' ?_
    filter_upwards [hev] with ε hε
    rw [if_pos hε]

end HRS.MS.UniqN2a
