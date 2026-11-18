import HRS.MS.R26T8AA01g
import HRS.MS.R26T8AP10a9

/-!
# S8.2 T8A A01 (part h): integrability of the canonical integrand and the coordinate kernels of `∇g`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The `j`-th coordinate of `∇g`. -/
def r26t8a_a01_kappa (d : ℕ) (j : Fin d) (w : Euc d) : ℝ := rieszKernelGrad d (criticalS d) w j

theorem r26t8a_a01_kappa_meas (j : Fin d) : Measurable (r26t8a_a01_kappa d j) :=
  ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable).comp (HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d))

theorem r26t8a_a01_kappa_odd (j : Fin d) (w : Euc d) : r26t8a_a01_kappa d j (-w) = -r26t8a_a01_kappa d j w := by
  unfold r26t8a_a01_kappa
  rw [HRS.MS.R2Interp.s102_rieszKernelGrad_neg]; rfl

theorem r26t8a_a01_kappa_bd (hs : 0 < criticalS d) (j : Fin d) {w : Euc d} (hw : w ≠ 0) :
    |r26t8a_a01_kappa d j w| ≤ criticalS d * ‖w‖ ^ (-criticalS d - 1) := by
  unfold r26t8a_a01_kappa
  have := r26t8a_abs_coord_le (rieszKernelGrad d (criticalS d) w) j
  rw [r26t8a_norm_rieszGrad hs hw] at this
  exact this

theorem r26t8a_a01_kappa_far (hs : 0 < criticalS d) (j : Fin d) :
    ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ w : Euc d, δ ≤ ‖w‖ → |r26t8a_a01_kappa d j w| ≤ B := by
  intro δ hδ
  refine ⟨criticalS d * δ ^ (-criticalS d - 1), fun w hw => ?_⟩
  have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ hw)
  refine (r26t8a_a01_kappa_bd hs j hw0).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hw (by linarith)) hs.le

set_option maxHeartbeats 3200000 in
theorem r26t8a_a01_canon_int (hd : 2 ≤ d) (hs : criticalS d < d) (hs0 : 0 < criticalS d)
    {φ : Euc d → ℝ} (hφm : AEStronglyMeasurable φ volume) (hφi : Integrable φ) {u : Euc d}
    {r1 : ℝ} (hr1 : 0 < r1) (hr14 : r1 ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z : Euc d, ‖z - u‖ < r1 → |φ z - φ u| ≤ L * ‖z - u‖) :
    Integrable (fun z => if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d (criticalS d) (u - z)
      else φ z • rieszKernelGrad d (criticalS d) (u - z)) := by
  set s := criticalS d with hsdef
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hae : ∀ᵐ z : Euc d ∂volume, z ≠ u := compl_mem_ae_iff.mpr (measure_singleton u)
  set Dm : Euc d → ℝ := fun z => (ball u r1).indicator (fun z => s * L * ‖z - u‖ ^ (-s)) z +
    s * r1 ^ (-s - 1) * |φ z| + (closedBall u (1 / 4)).indicator (fun _ => s * r1 ^ (-s - 1) * |φ u|) z with hDm
  have hDi : Integrable Dm := by
    refine Integrable.add (Integrable.add ?_ ?_) ?_
    · rw [integrable_indicator_iff measurableSet_ball]
      exact (r26t8a_p10a_pole_on hd hs0 hs u hr1).const_mul _
    · exact hφi.norm.const_mul _
    · rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const (by exact measure_closedBall_lt_top.ne)
  have hmeas : AEStronglyMeasurable (fun z => if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d s (u - z)
      else φ z • rieszKernelGrad d s (u - z)) volume := by
    have hk : AEStronglyMeasurable (fun z => rieszKernelGrad d s (u - z)) volume :=
      ((HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hsm : MeasurableSet {z : Euc d | ‖u - z‖ ≤ 1 / 4} :=
      measurableSet_le (measurable_const.sub measurable_id).norm measurable_const
    exact AEStronglyMeasurable.piecewise (s := {z : Euc d | ‖u - z‖ ≤ 1 / 4}) hsm
      (((hφm.sub aestronglyMeasurable_const).smul hk).restrict) ((hφm.smul hk).restrict)
  refine Integrable.mono' hDi hmeas ?_
  filter_upwards [hae] with z hz
  have hn : 0 < ‖u - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.symm)
  have hn' : ‖u - z‖ = ‖z - u‖ := norm_sub_rev _ _
  have hG := r26t8a_norm_rieszGrad hs0 (sub_ne_zero.2 hz.symm)
  have hp1 : 0 ≤ (ball u r1).indicator (fun z => s * L * ‖z - u‖ ^ (-s)) z :=
    Set.indicator_nonneg (fun v _ => by positivity) z
  have hp2 : 0 ≤ s * r1 ^ (-s - 1) * |φ z| := by positivity
  have hp3 : 0 ≤ (closedBall u (1 / 4)).indicator (fun _ => s * r1 ^ (-s - 1) * |φ u|) z :=
    Set.indicator_nonneg (fun v _ => by positivity) z
  by_cases h14 : ‖u - z‖ ≤ 1 / 4
  · rw [if_pos h14, norm_smul, Real.norm_eq_abs, hG]
    by_cases hr : ‖z - u‖ < r1
    · have h1 : |φ z - φ u| ≤ L * ‖z - u‖ := hlip z hr
      have hz1 : z ∈ ball u r1 := by rw [mem_ball, dist_eq_norm]; exact hr
      rw [hDm]; simp only
      rw [Set.indicator_of_mem hz1]
      have e : ‖u - z‖ ^ (-s - 1) = ‖z - u‖ ^ (-s - 1) := by rw [hn']
      have e2 : ‖z - u‖ * ‖z - u‖ ^ (-s - 1) = ‖z - u‖ ^ (-s) := by
        have hz0 : 0 < ‖z - u‖ := hn' ▸ hn
        rw [← Real.rpow_one_add' hz0.le (by linarith)]; congr 1; ring
      calc |φ z - φ u| * (s * ‖u - z‖ ^ (-s - 1))
          ≤ (L * ‖z - u‖) * (s * ‖u - z‖ ^ (-s - 1)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = s * L * ‖z - u‖ ^ (-s) := by rw [e, ← e2]; ring
        _ ≤ _ := by linarith
    · push Not at hr
      have hz1 : z ∈ closedBall u (1 / 4) := by rw [mem_closedBall, dist_eq_norm, ← hn']; linarith
      rw [hDm]; simp only
      rw [Set.indicator_of_mem hz1]
      have hrp : ‖u - z‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos hr1 (by rw [hn']; exact hr) (by linarith)
      calc |φ z - φ u| * (s * ‖u - z‖ ^ (-s - 1))
          ≤ (|φ z| + |φ u|) * (s * r1 ^ (-s - 1)) :=
            mul_le_mul (abs_sub _ _) (mul_le_mul_of_nonneg_left hrp hs0.le) (by positivity) (by positivity)
        _ = s * r1 ^ (-s - 1) * |φ z| + s * r1 ^ (-s - 1) * |φ u| := by ring
        _ ≤ _ := by linarith
  · rw [if_neg h14, norm_smul, Real.norm_eq_abs, hG]
    push Not at h14
    have hr : r1 ≤ ‖u - z‖ := by linarith
    have hrp : ‖u - z‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) := Real.rpow_le_rpow_of_nonpos hr1 hr (by linarith)
    have hz1 : z ∉ closedBall u (1 / 4) := by
      rw [mem_closedBall, dist_eq_norm, ← hn']; linarith
    have hz2 : z ∉ ball u r1 := by
      rw [mem_ball, dist_eq_norm, ← hn']; linarith
    rw [hDm]; simp only
    rw [Set.indicator_of_notMem hz1, Set.indicator_of_notMem hz2]
    calc |φ z| * (s * ‖u - z‖ ^ (-s - 1)) ≤ |φ z| * (s * r1 ^ (-s - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hs0.le) (abs_nonneg _)
      _ = s * r1 ^ (-s - 1) * |φ z| := by ring
      _ ≤ _ := by linarith

theorem r26t8a_a01_canon_int_coord (hd : 2 ≤ d) (hs : criticalS d < d) (hs0 : 0 < criticalS d) (j : Fin d)
    {φ : Euc d → ℝ} (hφm : AEStronglyMeasurable φ volume) (hφi : Integrable φ) {u : Euc d}
    {r1 : ℝ} (hr1 : 0 < r1) (hr14 : r1 ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z : Euc d, ‖z - u‖ < r1 → |φ z - φ u| ≤ L * ‖z - u‖) :
    Integrable (fun z => if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * r26t8a_a01_kappa d j (u - z)
      else φ z * r26t8a_a01_kappa d j (u - z)) := by
  have h := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (r26t8a_a01_canon_int hd hs hs0 hφm hφi hr1 hr14 hL hlip)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hc : ‖u - z‖ ≤ 1 / 4
  · show (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d (criticalS d) (u - z)
        else φ z • rieszKernelGrad d (criticalS d) (u - z)) =
        (if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * r26t8a_a01_kappa d j (u - z) else φ z * r26t8a_a01_kappa d j (u - z))
    rw [if_pos hc, if_pos hc]; simp [r26t8a_a01_kappa]
  · show (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) • rieszKernelGrad d (criticalS d) (u - z)
        else φ z • rieszKernelGrad d (criticalS d) (u - z)) =
        (if ‖u - z‖ ≤ 1 / 4 then (φ z - φ u) * r26t8a_a01_kappa d j (u - z) else φ z * r26t8a_a01_kappa d j (u - z))
    rw [if_neg hc, if_neg hc]; simp [r26t8a_a01_kappa]

end HRS.MS.R26T8A
