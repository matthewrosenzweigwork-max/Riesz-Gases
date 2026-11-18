import HRS.MS.R26T8AP10a16

/-!
# S8.2 T8A P10a (part 17): coordinates of the cancellation convolution `convGradConvW`
`r26t8a_p10a_conv_sum`: `∑_j (convGradConvW (∇g) (h_j) x)_j = ∫ Ecan0 s h x`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_norm_rieszGrad {s : ℝ} (hs : 0 < s) {w : Euc d} (hw : w ≠ 0) :
    ‖rieszKernelGrad d s w‖ = s * ‖w‖ ^ (-s - 1) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : rieszKernelGrad d s w = (-s * ‖w‖ ^ (-s - 2)) • w := by
    ext j
    rw [r26t8a_rieszGrad_coord hs.ne' hw j]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have h2 : ‖w‖ ^ (-s - 2) * ‖w‖ = ‖w‖ ^ (-s - 1) := by
    rw [← Real.rpow_add_one hn.ne']; congr 1; ring
  rw [h1, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _), mul_assoc, h2]

/-- The vector integrand of `convGradConvW (∇g) (h_j) x`. -/
def r26t8a_Fv (s : ℝ) (h : Euc d → Euc d) (x : Euc d) (j : Fin d) (u : Euc d) : Euc d :=
  if ‖x - u‖ ≤ 1 / 4 then (h u j - h x j) • rieszKernelGrad d s (x - u)
  else h u j • rieszKernelGrad d s (x - u)

theorem r26t8a_p10a_Fv_bound {s : ℝ} (hs : 0 < s) (hd1 : 1 ≤ d) {h : Euc d → Euc d} {x : Euc d} (j : Fin d)
    {r1 : ℝ} (hr1 : 0 < r1) (hr14 : r1 ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u : Euc d, ‖u - x‖ < r1 → ‖h u - h x‖ ≤ L * ‖u - x‖) {u : Euc d} (hu : u ≠ x) :
    ‖r26t8a_Fv s h x j u‖ ≤
      (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u +
      d * s * r1 ^ (-s - 1) * ‖h u‖ +
      (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u := by
  have hρ : 0 < ‖x - u‖ := norm_pos_iff.2 (sub_ne_zero.2 hu.symm)
  have hρ' : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hG := r26t8a_norm_rieszGrad hs (sub_ne_zero.2 hu.symm)
  have hp1 : 0 ≤ (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u :=
    Set.indicator_nonneg (fun v _ => by positivity) u
  have hp2 : 0 ≤ d * s * r1 ^ (-s - 1) * ‖h u‖ := by positivity
  have hp3 : 0 ≤ (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u :=
    Set.indicator_nonneg (fun v _ => by positivity) u
  have hbig : ‖x - u‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) ∨ ‖x - u‖ < r1 := by
    by_cases h' : r1 ≤ ‖x - u‖
    · exact Or.inl (Real.rpow_le_rpow_of_nonpos hr1 h' (by linarith))
    · exact Or.inr (not_le.1 h')
  unfold r26t8a_Fv
  by_cases hc : ‖x - u‖ ≤ 1 / 4
  · rw [if_pos hc, norm_smul, hG, Real.norm_eq_abs]
    have e1 : |h u j - h x j| ≤ ‖h u - h x‖ := by
      have := r26t8a_abs_coord_le (h u - h x) j
      simpa using this
    rcases hbig with hb | hb
    · have hm : u ∈ ball x (1 / 2) := by
        simp only [mem_ball_iff_norm, dist_eq_norm]; rw [← hρ']; linarith [hc]
      rw [Set.indicator_of_mem hm]
      have h3 : ‖h u - h x‖ ≤ ‖h u‖ + ‖h x‖ := norm_sub_le _ _
      have : |h u j - h x j| * (s * ‖x - u‖ ^ (-s - 1)) ≤ (‖h u‖ + ‖h x‖) * (s * r1 ^ (-s - 1)) := by
        gcongr
        exact e1.trans h3
      have h5 : (‖h u‖ + ‖h x‖) * (s * r1 ^ (-s - 1)) ≤
          d * s * r1 ^ (-s - 1) * ‖h u‖ + d * s * r1 ^ (-s - 1) * ‖h x‖ := by
        have : 0 ≤ s * r1 ^ (-s - 1) := by positivity
        nlinarith [norm_nonneg (h u), norm_nonneg (h x), mul_le_mul_of_nonneg_right hdd this]
      linarith
    · have hm : u ∈ ball x r1 := by
        simp only [mem_ball_iff_norm, dist_eq_norm]; rw [← hρ']; exact hb
      rw [Set.indicator_of_mem hm]
      have h3 := hlip u (by rw [← hρ']; exact hb)
      have h4 : ‖x - u‖ * ‖x - u‖ ^ (-s - 1) = ‖x - u‖ ^ (-s) := by
        rw [← Real.rpow_one_add' hρ.le (by linarith)]; congr 1; ring
      have : |h u j - h x j| * (s * ‖x - u‖ ^ (-s - 1)) ≤ (L * ‖u - x‖) * (s * ‖x - u‖ ^ (-s - 1)) := by
        gcongr
        exact e1.trans h3
      have h6 : (L * ‖u - x‖) * (s * ‖x - u‖ ^ (-s - 1)) = s * L * ‖u - x‖ ^ (-s) := by
        rw [← hρ', ← h4]; ring
      have h7 : s * L * ‖u - x‖ ^ (-s) ≤ d * s * L * ‖u - x‖ ^ (-s) := by
        have : 0 ≤ s * L * ‖u - x‖ ^ (-s) := by positivity
        nlinarith
      linarith
  · rw [if_neg hc, norm_smul, hG, Real.norm_eq_abs]
    have hr : ‖x - u‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hr1 (by linarith [not_le.1 hc]) (by linarith)
    have e1 : |h u j| ≤ ‖h u‖ := r26t8a_abs_coord_le (h u) j
    have : |h u j| * (s * ‖x - u‖ ^ (-s - 1)) ≤ ‖h u‖ * (s * r1 ^ (-s - 1)) := by gcongr
    have h5 : ‖h u‖ * (s * r1 ^ (-s - 1)) ≤ d * s * r1 ^ (-s - 1) * ‖h u‖ := by
      have : 0 ≤ s * r1 ^ (-s - 1) * ‖h u‖ := by positivity
      nlinarith
    linarith

theorem r26t8a_p10a_conv_sum {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) {x : Euc d} (hxy : x ≠ y) :
    ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun w => h w j) x) j =
      ∫ u, r26t8a_Ecan0 s h x u := by
  have hd := H.hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨r1, hr1, hr14, L, hL, hlip⟩ := r26t8a_p10a_lip H.C1 hxy
  have hhn := r26t8a_p10a_hnorm_int H
  have hBdi : Integrable (fun u =>
      (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u +
      d * s * r1 ^ (-s - 1) * ‖h u‖ +
      (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u) := by
    refine Integrable.add (Integrable.add ?_ ?_) ?_
    · rw [integrable_indicator_iff measurableSet_ball]
      exact (r26t8a_p10a_pole_on hd hs hsd x hr1).const_mul _
    · exact hhn.const_mul _
    · rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const (by exact measure_ball_lt_top.ne)
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  have hGm : Measurable (rieszKernelGrad d s) := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s
  have hFint : ∀ j : Fin d, Integrable (r26t8a_Fv s h x j) := by
    intro j
    have hhj : AEStronglyMeasurable (fun u => h u j) volume :=
      r26t8a_p10a_aesm hd y (((EuclideanSpace.proj j).continuous).comp_continuousOn H.C1.continuousOn)
    have hGx : AEStronglyMeasurable (fun u => rieszKernelGrad d s (x - u)) volume :=
      (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hsm : MeasurableSet {u : Euc d | ‖x - u‖ ≤ 1 / 4} :=
      measurableSet_le (measurable_const.sub measurable_id).norm measurable_const
    have hmeas : AEStronglyMeasurable (r26t8a_Fv s h x j) volume := by
      have := AEStronglyMeasurable.piecewise (s := {u : Euc d | ‖x - u‖ ≤ 1 / 4}) hsm
        (f := fun u => (h u j - h x j) • rieszKernelGrad d s (x - u))
        (g := fun u => h u j • rieszKernelGrad d s (x - u))
        (((hhj.sub aestronglyMeasurable_const).smul hGx).restrict)
        ((hhj.smul hGx).restrict)
      exact this
    refine Integrable.mono' hBdi hmeas ?_
    filter_upwards [hae] with u hu
    exact r26t8a_p10a_Fv_bound hs (by omega) j hr1 hr14 hL hlip hu
  have hcoord : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun w => h w j) x) j =
      ∫ u, (r26t8a_Fv s h x j u) j := by
    intro j
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm (hFint j)
    simpa [convGradConvW, r26t8a_Fv] using this.symm
  simp only [hcoord]
  have hint2 : ∀ j : Fin d, Integrable (fun u => (r26t8a_Fv s h x j u) j) := fun j =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (hFint j)
  rw [← integral_finset_sum _ fun j _ => hint2 j]
  refine integral_congr_ae ?_
  filter_upwards [hae] with u hu
  have hw : x - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  unfold r26t8a_Fv r26t8a_Ecan0
  by_cases hc : ‖x - u‖ ≤ 1 / 4
  · simp only [if_pos hc, PiLp.smul_apply, smul_eq_mul, r26t8a_rieszGrad_coord hs.ne' hw]
  · simp only [if_neg hc, PiLp.smul_apply, smul_eq_mul, r26t8a_rieszGrad_coord hs.ne' hw]

end HRS.MS.R26T8A
