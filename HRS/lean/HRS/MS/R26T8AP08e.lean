import HRS.MS.R26T8AP08d
import HRS.MS.R26T8AP11a

/-!
# S8.2 T8A P08 (part e): `∫ a(y) (1 + |x-y|^(-s)) dy` is bounded uniformly in `x` for bounded integrable `a`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f25_conv_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) :
    ∃ Ω : ℝ, 0 ≤ Ω ∧ ∀ (a : Euc d → ℝ) (Ka : ℝ), (∀ y, 0 ≤ a y) → (∀ y, a y ≤ Ka) → Continuous a →
      Integrable a → ∀ x : Euc d, Integrable (fun y => a y * (1 + ‖x - y‖ ^ (-s))) ∧
        ∫ y, a y * (1 + ‖x - y‖ ^ (-s)) ≤ 3 * (∫ y, a y) + Ka * Ω := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  obtain ⟨hmI, hmV⟩ := r26t8a_p11a_mass d hd ((d : ℝ) - s) (by linarith) (by linarith) 1 one_pos
  have hexp : (d : ℝ) - s - d = -s := by ring
  rw [hexp] at hmI hmV
  set Ω : ℝ := sphereArea d * ((1 : ℝ) ^ ((d : ℝ) - s) / ((d : ℝ) - s)) with hΩ
  have hΩ0 : 0 ≤ Ω := by
    have : 0 ≤ ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-s) :=
      setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
    rwa [hmV] at this
  refine ⟨Ω, hΩ0, fun a Ka ha0 haK hac hai x => ?_⟩
  have hKa : 0 ≤ Ka := (ha0 0).trans (haK 0)
  -- the pole term, dominated by `Ka 1_ball |x-y|^(-s) + a`
  set P : Euc d → ℝ := fun y => (ball x 1).indicator (fun y => Ka * ‖x - y‖ ^ (-s)) y + a y with hP
  have hpole : Integrable (fun y : Euc d => ‖x - y‖ ^ (-s)) (volume.restrict (ball x 1)) := by
    have h1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (ball (0 : Euc d) 1) := hmI
    have h2 := (h1.integrable_indicator measurableSet_ball).comp_sub_left x
    refine (integrable_indicator_iff measurableSet_ball).1 ?_
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ ball x 1
    · have : x - y ∈ ball (0 : Euc d) 1 := by
        simpa [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev] using hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : x - y ∉ ball (0 : Euc d) 1 := by
        simpa [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev] using hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  have hPi : Integrable P := by
    refine Integrable.add ?_ hai
    exact (integrable_indicator_iff measurableSet_ball).2 (hpole.const_mul Ka)
  have hmeas : AEStronglyMeasurable (fun y => a y * (1 + ‖x - y‖ ^ (-s))) volume :=
    hac.aestronglyMeasurable.mul (aestronglyMeasurable_const.add
      ((measurable_const.sub measurable_id).norm.pow_const _).aestronglyMeasurable)
  have hdom : ∀ y, ‖a y * (1 + ‖x - y‖ ^ (-s))‖ ≤ 2 * a y + P y := by
    intro y
    have hk : 0 ≤ ‖x - y‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_of_nonneg (mul_nonneg (ha0 y) (by linarith))]
    by_cases hy : y ∈ ball x 1
    · have hP' : P y = Ka * ‖x - y‖ ^ (-s) + a y := by rw [hP]; simp only [Set.indicator_of_mem hy]
      rw [hP']
      nlinarith [mul_le_mul_of_nonneg_right (haK y) hk, ha0 y]
    · have hP' : P y = a y := by rw [hP]; simp only [Set.indicator_of_notMem hy, zero_add]
      have hy1 : 1 ≤ ‖x - y‖ := by
        simpa [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev, not_lt] using hy
      have : ‖x - y‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
      rw [hP']
      nlinarith [mul_le_mul_of_nonneg_left this (ha0 y), ha0 y]
  have hsum : Integrable (fun y => 2 * a y + P y) := (hai.const_mul 2).add hPi
  have hint : Integrable (fun y => a y * (1 + ‖x - y‖ ^ (-s))) :=
    Integrable.mono' hsum hmeas (Filter.Eventually.of_forall hdom)
  refine ⟨hint, ?_⟩
  refine (integral_mono hint hsum (fun y => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hdom y))).trans ?_
  rw [integral_add (hai.const_mul 2) hPi, integral_const_mul]
  have hP1 : ∫ y, P y = (∫ y, a y) + Ka * Ω := by
    rw [hP, integral_add ((integrable_indicator_iff measurableSet_ball).2 (hpole.const_mul Ka)) hai,
      integral_indicator measurableSet_ball, integral_const_mul]
    have : ∫ y in ball x 1, ‖x - y‖ ^ (-s) = Ω := by
      rw [← hmV]
      have h3 := integral_sub_left_eq_self
        (fun z : Euc d => (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z) volume x
      rw [integral_indicator measurableSet_ball] at h3
      rw [← h3, ← integral_indicator measurableSet_ball]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ ball x 1
      · have : x - y ∈ ball (0 : Euc d) 1 := by
          simpa [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev] using hy
        simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
      · have : x - y ∉ ball (0 : Euc d) 1 := by
          simpa [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev] using hy
        simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
    rw [this]; ring
  rw [hP1]; linarith

end HRS.MS.R26T8A
