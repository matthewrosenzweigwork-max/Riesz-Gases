import HRS.MS.SA16Y3Hk1
import HRS.MS.SA16Y3Sk3

/-!
# S.A.16 (SA16Y3) Hk2: the commutator `Q^i(a w) - a Q^i w` as an absolutely convergent integral (packet P7, Hilbert corner)

`sa16y3_kk s B L`: the `L^1` majorant `c_s L |z|^{-s} 1_{|z|<1} + 2 c_s B 2^{s+1} (1+|z|)^{-(s+1)}` (`s + 1 > d`).
`sa16y3_comm_formula`: `Q^i(aw)(x) - a(x) Q^i w(x) = ∫ K_i(z) (a(x-z) - a(x)) w(x-z) dz`.
`sa16y3_comm_bound`: `|Q^i(aw)(x) - a(x) Q^i w(x)| ≤ ∫ k(z) |w(x-z)| dz`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hk2
variable {d : ℕ} {s : ℝ}

/-- the `L^1` majorant of the commutator kernel -/
def sa16y3_kk (s B L : ℝ) (z : Euc d) : ℝ :=
  (ball (0 : Euc d) 1).indicator (fun z => HRS.CZ.Hls.hlsg_c s * L * ‖z‖ ^ (-s)) z +
    HRS.CZ.Hls.hlsg_c s * (2 * B) * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1))

lemma sa16y3_kk_nonneg (hs0 : 0 ≤ s) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (z : Euc d) : 0 ≤ sa16y3_kk s B L z := by
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs0
  unfold sa16y3_kk
  refine add_nonneg (indicator_nonneg (fun z _ => ?_) z) (by positivity)
  positivity

lemma sa16y3_kk_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) (B L : ℝ) :
    Integrable (sa16y3_kk s B L : Euc d → ℝ) := by
  have h1 : Integrable ((ball (0 : Euc d) 1).indicator (fun z : Euc d => HRS.CZ.Hls.hlsg_c s * L * ‖z‖ ^ (-s))) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((HRS.S16Frac.s16frac_integrableOn_ball_rpow (d := d) hd (α := s) hsd 1).const_mul
        (HRS.CZ.Hls.hlsg_c s * L))
  have h2 : Integrable (fun z : Euc d => (1 + ‖z‖) ^ (-(s + 1))) :=
    integrable_one_add_norm (μ := (volume : Measure (Euc d))) (by rw [finrank_euclideanSpace_fin]; exact hθ)
  exact h1.add (h2.const_mul _)

lemma sa16y3_kk_bound (hs0 : 0 ≤ s) {a w : Euc d → ℝ} {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L)
    (ha : ContDiff ℝ ∞ a) (hB : ∀ y, |a y| ≤ B) (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ L) (i : Fin d) (x z : Euc d) :
    |sa16z_Kx s i z * ((a (x - z) - a x) * w (x - z))| ≤ sa16y3_kk s B L z * |w (x - z)| := by
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hkk := sa16y3_kk_nonneg hs0 (d := d) hB0 hL0 z
  by_cases hz : z = 0
  · subst hz
    have h0 : sa16z_Kx s i (0 : Euc d) = 0 := by simp [sa16z_Kx]
    rw [h0, zero_mul, abs_zero]
    exact mul_nonneg hkk (abs_nonneg _)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hK := sa16z_Kx_bound hs0 i hz
  have hLip : |a (x - z) - a x| ≤ L * ‖z‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := a) (s := (univ : Set (Euc d))) (C := L)
      (fun y _ => (ha.differentiable (by simp)) y) (fun y _ => hL y) convex_univ (mem_univ x) (mem_univ (x - z))
    simpa [Real.norm_eq_abs] using this
  have h2B : |a (x - z) - a x| ≤ 2 * B := by
    calc |a (x - z) - a x| ≤ |a (x - z)| + |a x| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring
  rw [abs_mul, abs_mul]
  have hwa := abs_nonneg (w (x - z))
  have hd0 := abs_nonneg (a (x - z) - a x)
  have hKn := abs_nonneg (sa16z_Kx s i z)
  have step : |sa16z_Kx s i z| * |a (x - z) - a x| ≤ sa16y3_kk s B L z := by
    by_cases hz1 : ‖z‖ < 1
    · have hmem : z ∈ ball (0 : Euc d) 1 := by simpa using hz1
      have h3 : |sa16z_Kx s i z| * |a (x - z) - a x| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) * (L * ‖z‖) :=
        mul_le_mul hK hLip hd0 (by positivity)
      have h4 : HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) * (L * ‖z‖) = HRS.CZ.Hls.hlsg_c s * L * ‖z‖ ^ (-s) := by
        have : ‖z‖ ^ (-s) = ‖z‖ ^ (-s - 1) * ‖z‖ := by
          conv_lhs => rw [show -s = (-s - 1) + 1 by ring]
          rw [Real.rpow_add hzpos, Real.rpow_one]
        rw [this]; ring
      have h5 : HRS.CZ.Hls.hlsg_c s * L * ‖z‖ ^ (-s) ≤ sa16y3_kk s B L z := by
        unfold sa16y3_kk
        simp only [indicator_of_mem hmem]
        have : 0 ≤ HRS.CZ.Hls.hlsg_c s * (2 * B) * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) := by positivity
        linarith
      linarith
    · have hz1' : 1 ≤ ‖z‖ := not_lt.1 hz1
      have h3 : |sa16z_Kx s i z| * |a (x - z) - a x| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) * (2 * B) :=
        mul_le_mul hK h2B hd0 (by positivity)
      have hnb : ‖z‖ ^ (-(s + 1)) ≤ (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) := by
        have h6 : (2 * ‖z‖) ^ (-(s + 1)) ≤ (1 + ‖z‖) ^ (-(s + 1)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        rw [Real.mul_rpow (by norm_num) hzpos.le] at h6
        have h7 : (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-(s + 1)) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; simp
        have h8 : 0 ≤ ‖z‖ ^ (-(s + 1)) := by positivity
        have h9 : 0 < (2 : ℝ) ^ (s + 1) := by positivity
        calc ‖z‖ ^ (-(s + 1)) = (2 : ℝ) ^ (s + 1) * ((2 : ℝ) ^ (-(s + 1)) * ‖z‖ ^ (-(s + 1))) := by
              rw [← mul_assoc, h7, one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left h6 h9.le
      have h5 : HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) * (2 * B) ≤ sa16y3_kk s B L z := by
        have e : ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-(s + 1)) := by congr 1; ring
        rw [e]
        unfold sa16y3_kk
        have hnm : z ∉ ball (0 : Euc d) 1 := by simpa using hz1'
        rw [indicator_of_notMem hnm, zero_add]
        calc HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-(s + 1)) * (2 * B)
            = HRS.CZ.Hls.hlsg_c s * (2 * B) * ‖z‖ ^ (-(s + 1)) := by ring
          _ ≤ HRS.CZ.Hls.hlsg_c s * (2 * B) * ((2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1))) :=
              mul_le_mul_of_nonneg_left hnb (by positivity)
          _ = _ := by ring
      linarith
  calc |sa16z_Kx s i z| * (|a (x - z) - a x| * |w (x - z)|)
      = (|sa16z_Kx s i z| * |a (x - z) - a x|) * |w (x - z)| := by ring
    _ ≤ sa16y3_kk s B L z * |w (x - z)| := mul_le_mul_of_nonneg_right step hwa

lemma sa16y3_trunc_int (hs0 : 0 ≤ s) (i : Fin d) {u : Euc d → ℝ} (hu : IsCcInfty u) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z => sa16z_Kx s i z * u z) {z : Euc d | ε < ‖z‖} := by
  have hS : MeasurableSet {z : Euc d | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hint : Integrable u := hu.1.continuous.integrable_of_hasCompactSupport hu.2
  have hg : IntegrableOn (fun z => (HRS.CZ.Hls.hlsg_c s * ε ^ (-s - 1)) * ‖u z‖) {z : Euc d | ε < ‖z‖} :=
    (hint.norm.const_mul _).integrableOn
  refine Integrable.mono' hg ((sa16z_Kx_meas s i).mul hu.1.continuous.measurable).aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem hS fun z hz => ?_
  have hz' : ε ≤ ‖z‖ := le_of_lt hz
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (sa16z_Kx_bound_far hs0 i hε hz') (norm_nonneg _)

theorem sa16y3_comm_formula (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {a w : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : IsCcInfty w) {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hB : ∀ y, |a y| ≤ B)
    (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ L) (i : Fin d) (x : Euc d) :
    sa16y3_Q s i (fun y => a y * w y) x - a x * sa16y3_Q s i w x =
      ∫ z, sa16z_Kx s i z * ((a (x - z) - a x) * w (x - z)) := by
  have hf : IsCcInfty (fun y => a y * w y) := sa16y3_bmul_cc ha hw
  have T1 := sa16z_pv_tendsto hd hs0 hsd hf i x
  have T2 := (sa16z_pv_tendsto hd hs0 hsd hw i x).const_mul (a x)
  have T := T1.sub T2
  obtain ⟨M, hM⟩ := hw.1.continuous.bounded_above_of_compact_support hw.2
  set F : Euc d → ℝ := fun z => sa16z_Kx s i z * ((a (x - z) - a x) * w (x - z)) with hF
  have hFm : Measurable F := by
    refine (sa16z_Kx_meas s i).mul ?_
    have h1 : Continuous fun z : Euc d => a (x - z) := ha.continuous.comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun z : Euc d => w (x - z) := hw.1.continuous.comp (continuous_const.sub continuous_id)
    exact ((h1.sub continuous_const).mul h2).measurable
  have hFb : ∀ z, ‖F z‖ ≤ sa16y3_kk s B L z * M := fun z => by
    rw [Real.norm_eq_abs]
    refine (sa16y3_kk_bound hs0 hB0 hL0 ha hB hL i x z).trans ?_
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM (x - z))
      (sa16y3_kk_nonneg hs0 hB0 hL0 z)
  have hbint : Integrable (fun z => sa16y3_kk s B L z * M) :=
    (sa16y3_kk_integrable hd hs0 hsd hθ B L).mul_const M
  have hFint : Integrable F := hbint.mono' hFm.aestronglyMeasurable (Eventually.of_forall hFb)
  -- truncated integrals converge to the full integral
  have hlim : Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, F z) (𝓝[>] 0) (𝓝 (∫ z, F z)) := by
    have hS : ∀ ε : ℝ, MeasurableSet {z : Euc d | ε < ‖z‖} := fun ε => measurableSet_lt measurable_const measurable_norm
    simp_rw [← integral_indicator (hS _)]
    refine tendsto_integral_filter_of_dominated_convergence (fun z => sa16y3_kk s B L z * M)
      (Eventually.of_forall fun ε => (hFm.indicator (hS ε)).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun z => ?_) hbint (Eventually.of_forall fun z => ?_)
    · by_cases hz : z ∈ {z : Euc d | ε < ‖z‖}
      · rw [indicator_of_mem hz]; exact hFb z
      · rw [indicator_of_notMem hz, norm_zero]
        exact mul_nonneg (sa16y3_kk_nonneg hs0 hB0 hL0 z) ((norm_nonneg _).trans (hM 0))
    · by_cases hz : z = 0
      · subst hz
        have h00 : F 0 = 0 := by simp [hF, sa16z_Kx]
        have h0 : ∀ ε : ℝ, Set.indicator {z : Euc d | ε < ‖z‖} F 0 = 0 := fun ε => by
          by_cases h : (0 : Euc d) ∈ {z : Euc d | ε < ‖z‖}
          · rw [indicator_of_mem h]; exact h00
          · rw [indicator_of_notMem h]
        rw [h00]
        simp only [h0]
        exact tendsto_const_nhds
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hzpos] with ε hε
        rw [indicator_of_mem (show z ∈ {z : Euc d | ε < ‖z‖} from hε.2)]
  have heq : (fun ε : ℝ => (∫ z in {z : Euc d | ε < ‖z‖}, sa16z_Kx s i z * (fun y => a y * w y) (x - z)) -
        a x * ∫ z in {z : Euc d | ε < ‖z‖}, sa16z_Kx s i z * w (x - z)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, F z := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have i1 := sa16y3_trunc_int hs0 i (sa16z_F_cc hf x) hε'
    have i2 := sa16y3_trunc_int hs0 i (sa16z_F_cc hw x) hε'
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
    simp only [hF]
    ring
  exact tendsto_nhds_unique_of_eventuallyEq T hlim heq

theorem sa16y3_comm_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {a w : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : IsCcInfty w) {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hB : ∀ y, |a y| ≤ B)
    (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ L) (i : Fin d) (x : Euc d) :
    |sa16y3_Q s i (fun y => a y * w y) x - a x * sa16y3_Q s i w x| ≤
      ∫ z, sa16y3_kk s B L z * |w (x - z)| := by
  rw [sa16y3_comm_formula hd hs0 hsd hθ ha hw hB0 hL0 hB hL i x]
  obtain ⟨M, hM⟩ := hw.1.continuous.bounded_above_of_compact_support hw.2
  have hint : Integrable (fun z : Euc d => sa16y3_kk s B L z * |w (x - z)|) := by
    refine (sa16y3_kk_integrable hd hs0 hsd hθ B L).mul_bdd ?_ ?_ (c := M)
    · exact (hw.1.continuous.comp (continuous_const.sub continuous_id)).abs.aestronglyMeasurable
    · exact Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM (x - z)
  refine (abs_integral_le_integral_abs).trans ?_
  exact integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hint
    (Eventually.of_forall fun z => sa16y3_kk_bound hs0 hB0 hL0 ha hB hL i x z)

end Hk2

end HRS.Whole.AppendixA.Phase2SA16R
