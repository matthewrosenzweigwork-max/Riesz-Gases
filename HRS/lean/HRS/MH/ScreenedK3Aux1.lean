import HRS.MH.ScreenedDefs
import HRS.Whole.MovtrAux4
import HRS.Whole.Q34Aux1

/-! Packet K3 (`gk_weak`), auxiliary 1: integrability of `‖x - y‖^a |h x|` for `-d < a ≤ 0`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma k3_ae_ne (hd : 1 ≤ d) (y : Euc d) : ∀ᵐ x ∂(volume : Measure (Euc d)), x ≠ y := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  exact compl_mem_ae_iff.mpr (measure_singleton y)

/-- Local integrability of `‖u‖^a` on the unit ball, for `-d < a ≤ 0`. -/
lemma k3_indicator_integrable (hd : 1 ≤ d) {a : ℝ} (ha0 : a ≤ 0) (ha : -(d : ℝ) < a) :
    Integrable (Set.indicator (Metric.ball (0 : Euc d) 1) (fun u : Euc d => ‖u‖ ^ a)) := by
  have hmeas : Measurable (fun u : Euc d => ‖u‖ ^ a) := measurable_norm.pow_const a
  rw [integrable_indicator_iff measurableSet_ball]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have key := HRS.Whole.Q34.lintegral_ball_rpow (d := d) hd (a := -a) one_pos (by linarith)
  simp only [neg_neg] at key
  have hcongr : ∀ u : Euc d, ‖‖u‖ ^ a‖ₑ = ENNReal.ofReal (‖u‖ ^ a) := by
    intro u
    rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) a)]
  simp only [hcongr]
  rw [key]
  exact ENNReal.ofReal_lt_top

/-- `‖x - y‖^a |h x|` is integrable for a bounded continuous `h` with `|h|` integrable, `-d < a ≤ 0`. -/
lemma k3_integrable_rpow (hd : 1 ≤ d) {a : ℝ} (ha0 : a ≤ 0) (ha : -(d : ℝ) < a) (y : Euc d)
    {h : Euc d → ℝ} (hc : Continuous h) (hb : ∃ M, ∀ x, ‖h x‖ ≤ M)
    (h0 : Integrable fun x => ‖h x‖) :
    Integrable fun x => ‖x - y‖ ^ a * ‖h x‖ := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hH := (k3_indicator_integrable hd ha0 ha).comp_sub_right y
  refine Integrable.mono' ((hH.const_mul M).add h0) ?_ ?_
  · exact (((measurable_norm.comp (measurable_id.sub_const y)).pow_const a).mul
      hc.norm.measurable).aestronglyMeasurable
  · refine Eventually.of_forall (fun x => ?_)
    have hpow : 0 ≤ ‖x - y‖ ^ a := Real.rpow_nonneg (norm_nonneg _) a
    rw [norm_mul, Real.norm_of_nonneg hpow, norm_norm]
    dsimp only [Pi.add_apply]
    by_cases hx : ‖x - y‖ < 1
    · have hmem : x - y ∈ Metric.ball (0 : Euc d) 1 := by
        rw [mem_ball_zero_iff]; exact hx
      have hind : Set.indicator (Metric.ball (0 : Euc d) 1) (fun u : Euc d => ‖u‖ ^ a) (x - y)
          = ‖x - y‖ ^ a := Set.indicator_of_mem hmem _
      rw [hind]
      have := mul_le_mul_of_nonneg_left (hM x) hpow
      have := norm_nonneg (h x)
      linarith
    · have hnmem : x - y ∉ Metric.ball (0 : Euc d) 1 := by
        rw [mem_ball_zero_iff]; exact hx
      have hind : Set.indicator (Metric.ball (0 : Euc d) 1) (fun u : Euc d => ‖u‖ ^ a) (x - y) = 0 :=
        Set.indicator_of_notMem hnmem _
      have hle : ‖x - y‖ ^ a ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_gt hx) ha0
      rw [hind]
      have := mul_le_mul_of_nonneg_right hle (norm_nonneg (h x))
      linarith

end HRS.MH.Screened
