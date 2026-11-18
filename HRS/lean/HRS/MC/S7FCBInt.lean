import HRS.MC.S7FCBBall

/-!
# FC-B, part 3: ball integral of the profile and `L^p` integrability

`fcb_ball_lintegral`: `∫_{‖v‖<ϱ} Phi(‖v‖) dv ≤ J ϱ^d Phi(ϱ)` on the torus, `0 < ϱ ≤ 1/2`.
`fcb_lintegral_Phi_rpow`: `Phi(‖·‖)^p` is integrable when `p s < d`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

theorem fcb_measurable_Phi (s : ℝ) : Measurable (fcbPhi s) := by
  unfold fcbPhi singEnvelope
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    exact measurable_const.add (Real.measurable_log.comp (measurable_id.min measurable_const)).abs
  · simp only [h0, if_false]
    exact measurable_const.add ((measurable_id.min measurable_const).pow_const _)

theorem fcb_measurable_Phi_norm (s : ℝ) {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] : Measurable (fun v : E => fcbPhi s ‖v‖) :=
  (fcb_measurable_Phi s).comp measurable_norm

/-- the integral of `Phi(‖y‖)` over the unit ball of `ℝ^d` (sup norm) is finite. -/
theorem fcb_unit_ball_finite (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) :
    ∫⁻ y in ball (0 : Fin d → ℝ) 1, ENNReal.ofReal (fcbPhi s ‖y‖) < ⊤ := by
  set α : ℝ := (s + d) / 2 with hα
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hα0 : 0 < α := by rw [hα]; linarith
  obtain ⟨A, hA, hAle⟩ := fcb_Phi_le_rpow hs0 hα0 (show s ≤ α by rw [hα]; linarith)
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  have hint : IntegrableOn (fun y : Fin d → ℝ => fcbPhi s ‖y‖) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (Fin d → ℝ))) (C := A) (α := α)
      (r := 1) (by rw [hfin]; exact hd) (by rw [hfin]; rw [hα]; linarith) ?_
      (fcb_measurable_Phi_norm s).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (ae_ne_pi hd), ae_restrict_mem measurableSet_ball] with y hy0 hy
    have hy1 : ‖y‖ < 1 := by simpa using hy
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [Real.norm_eq_abs, abs_of_pos (fcb_Phi_pos hs0 hpos)]
    exact hAle _ hpos hy1.le
  exact lt_of_le_of_lt (lintegral_mono fun y => Real.ofReal_le_enorm _) hint.2

/-- the main ball estimate -/
theorem fcb_ball_lintegral (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) :
    ∃ J : ℝ, 0 < J ∧ ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ 1 / 2 →
      ∫⁻ v : Torus d, {v : Torus d | ‖v‖ < ϱ}.indicator (fun v => ENNReal.ofReal (fcbPhi s ‖v‖)) v
        ≤ ENNReal.ofReal (J * ϱ ^ d * fcbPhi s ϱ) := by
  set J0 : ℝ≥0∞ := ∫⁻ y in ball (0 : Fin d → ℝ) (1 / 2), ENNReal.ofReal (fcbPhi s ‖y‖) with hJ0
  have hJ0fin : J0 < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (ball_subset_ball (by norm_num))) (fcb_unit_ball_finite hd hs0 hs)
  refine ⟨2 ^ d * (J0.toReal + 1), by positivity, fun ϱ hϱ hϱ2 => ?_⟩
  set G : (Fin d → ℝ) → ℝ≥0∞ :=
    {y : Fin d → ℝ | ‖y‖ < ϱ}.indicator (fun y => ENNReal.ofReal (fcbPhi s ‖y‖)) with hG
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_norm measurable_const)
    exact ENNReal.measurable_ofReal.comp (fcb_measurable_Phi_norm s)
  -- torus -> box -> whole space
  have h1 : ∫⁻ v : Torus d, {v : Torus d | ‖v‖ < ϱ}.indicator
      (fun v => ENNReal.ofReal (fcbPhi s ‖v‖)) v ≤ ∫⁻ y, G y := by
    rw [lintegral_torus_box]
    refine le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)
    filter_upwards [ae_restrict_mem (measurableSet_Box d)] with y hy
    have hn : ‖boxPt y‖ = ‖y‖ := HRS.Commutator.SliceAux.norm_boxPt_eq (fun i => Box_abs_le hy i)
    simp only [hG, Set.indicator, Set.mem_setOf_eq, hn]
    exact le_rfl
  -- scaling by `2ϱ`
  set r : ℝ := 2 * ϱ with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr0' : r ≠ 0 := hr0.ne'
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  have h2 : ∫⁻ y, G y = ENNReal.ofReal (r ^ d) * ∫⁻ y, G (r • y) := by
    have hmap := Measure.map_addHaar_smul (volume : Measure (Fin d → ℝ)) hr0'
    have h3 : ∫⁻ y, G y ∂(Measure.map (fun x : Fin d → ℝ => r • x) volume) = ∫⁻ y, G (r • y) :=
      lintegral_map hGm (measurable_const_smul r)
    rw [hmap, lintegral_smul_measure, hfin, smul_eq_mul] at h3
    have h4 : ENNReal.ofReal |(r ^ d)⁻¹| * ENNReal.ofReal (r ^ d) = 1 := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity), inv_mul_cancel₀ (by positivity)]
      simp
    calc ∫⁻ y, G y = (ENNReal.ofReal |(r ^ d)⁻¹| * ENNReal.ofReal (r ^ d)) * ∫⁻ y, G y := by
          rw [h4, one_mul]
      _ = ENNReal.ofReal (r ^ d) * (ENNReal.ofReal |(r ^ d)⁻¹| * ∫⁻ y, G y) := by ring
      _ = _ := by rw [h3]
  have h5 : ∫⁻ y, G (r • y) ≤ ENNReal.ofReal (fcbPhi s ϱ) * J0 := by
    rw [hJ0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_ball]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_ne_pi hd] with y hy0
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hn : ‖r • y‖ = r * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
    by_cases hy : ‖y‖ < 1 / 2
    · have hyb : y ∈ ball (0 : Fin d → ℝ) (1 / 2) := by simpa using hy
      have hlt : ‖r • y‖ < ϱ := by rw [hn, hr]; nlinarith
      simp only [hG, Set.indicator, Set.mem_setOf_eq, hlt, if_true, hyb]
      rw [← ENNReal.ofReal_mul (fcb_Phi_pos hs0 hϱ).le, hn]
      refine ENNReal.ofReal_le_ofReal ?_
      have h6 := fcb_Phi_submul hs0 hr0 hpos hy.le
      have h7 : fcbPhi s r ≤ fcbPhi s ϱ := fcb_Phi_anti hs0 hϱ (by rw [hr]; linarith)
      calc fcbPhi s (r * ‖y‖) ≤ fcbPhi s r * fcbPhi s ‖y‖ := h6
        _ ≤ fcbPhi s ϱ * fcbPhi s ‖y‖ :=
          mul_le_mul_of_nonneg_right h7 (fcb_Phi_pos hs0 hpos).le
    · have hnl : ¬ ‖r • y‖ < ϱ := by
        rw [hn, not_lt]; push Not at hy; rw [hr]; nlinarith
      simp [hG, Set.indicator, hnl]
  calc ∫⁻ v : Torus d, {v : Torus d | ‖v‖ < ϱ}.indicator
        (fun v => ENNReal.ofReal (fcbPhi s ‖v‖)) v ≤ ∫⁻ y, G y := h1
    _ = ENNReal.ofReal (r ^ d) * ∫⁻ y, G (r • y) := h2
    _ ≤ ENNReal.ofReal (r ^ d) * (ENNReal.ofReal (fcbPhi s ϱ) * J0) := by gcongr
    _ ≤ ENNReal.ofReal (r ^ d) * (ENNReal.ofReal (fcbPhi s ϱ) * ENNReal.ofReal (J0.toReal + 1)) := by
        have hJ : J0 ≤ ENNReal.ofReal (J0.toReal + 1) :=
          (ENNReal.ofReal_toReal hJ0fin.ne).symm.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
        gcongr
    _ = ENNReal.ofReal (2 ^ d * (J0.toReal + 1) * ϱ ^ d * fcbPhi s ϱ) := by
        rw [← ENNReal.ofReal_mul (fcb_Phi_pos hs0 hϱ).le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hr, mul_pow]; ring

/-- `Phi(‖v‖)^p` is integrable on the torus when `p s < d`. -/
theorem fcb_lintegral_Phi_rpow (hd : 0 < d) {s p : ℝ} (hs0 : 0 ≤ s) (hp : 0 < p) (hps : p * s < d) :
    ∫⁻ v : Torus d, ENNReal.ofReal (fcbPhi s ‖v‖) ^ p < ⊤ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set α : ℝ := (s + d / p) / 2 with hα
  have hdp : 0 < (d : ℝ) / p := by positivity
  have hsdp : s < d / p := by rw [lt_div_iff₀ hp]; linarith
  have hα0 : 0 < α := by rw [hα]; linarith
  have hsα : s ≤ α := by rw [hα]; linarith
  have hαp : α * p < d := by
    have : α * p = (s * p + d) / 2 := by rw [hα]; field_simp
    rw [this]; linarith
  obtain ⟨A, hA, hAle⟩ := fcb_Phi_le_rpow hs0 hα0 hsα
  rw [lintegral_torus_box]
  have hI := integrableOn_Box_rpow hd hαp
  have hfin : ∫⁻ y in Box d, ENNReal.ofReal (A ^ p * ‖y‖ ^ (-(α * p))) < ⊤ := by
    have := (hI.const_mul (A ^ p)).2
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) this
    rw [Real.enorm_of_nonneg (by positivity)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [ae_restrict_of_ae (ae_ne_pi hd), ae_restrict_mem (measurableSet_Box d)] with y hy0 hy
  have hn : ‖boxPt y‖ = ‖y‖ := HRS.Commutator.SliceAux.norm_boxPt_eq (fun i => Box_abs_le hy i)
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hle : ‖y‖ ≤ 1 := (Box_norm_le hy).trans (by norm_num)
  rw [hn]
  have h1 := hAle ‖y‖ hpos hle
  rw [ENNReal.ofReal_rpow_of_nonneg (fcb_Phi_pos hs0 hpos).le hp.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc fcbPhi s ‖y‖ ^ p ≤ (A * ‖y‖ ^ (-α)) ^ p :=
        Real.rpow_le_rpow (fcb_Phi_pos hs0 hpos).le h1 hp.le
    _ = A ^ p * ‖y‖ ^ (-(α * p)) := by
        rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul hpos.le]
        congr 2; ring

end HRS.MC.Sec7.FCB
