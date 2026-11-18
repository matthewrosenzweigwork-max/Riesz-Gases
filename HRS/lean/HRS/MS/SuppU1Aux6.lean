import HRS.MS.SuppU1Aux5

/-!
# U1 aux 6: integrability of the profile against bounded-density probability measures, and of
cut-off kernels against Haar measure.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma u1_lintegral_Vs_shift_meas {s r M : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (μ' : Measure E)
    (hle : μ' ≤ ENNReal.ofReal M • μ) (x : E) {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in ball x a, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂μ'
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (a ^ Module.finrank ℝ E * u1Vs s a ^ r) * u1J μ s r) := by
  calc ∫⁻ y in ball x a, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂μ'
      ≤ ∫⁻ y in ball x a, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂(ENNReal.ofReal M • μ) :=
        lintegral_mono' (Measure.restrict_mono le_rfl hle) le_rfl
    _ = ENNReal.ofReal M * ∫⁻ y in ball x a, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂μ := by
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by
        gcongr
        exact u1_lintegral_Vs_shift μ hs hr x ha

lemma u1_lintegral_prod_Vs {s r M : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hrs : r * s < (Module.finrank ℝ E : ℝ)) (μ' : Measure E) [IsProbabilityMeasure μ']
    (hle : μ' ≤ ENNReal.ofReal M • μ) :
    ∫⁻ p : E × E, ENNReal.ofReal (u1Vs s ‖p.1 - p.2‖ ^ r) ∂(μ'.prod μ') ≠ ⊤ := by
  have hmeas : Measurable (fun p : E × E => ENNReal.ofReal (u1Vs s ‖p.1 - p.2‖ ^ r)) :=
    ENNReal.measurable_ofReal.comp (((u1Vs_measurable (E := E) s).comp
      (measurable_fst.sub measurable_snd)).pow_const r)
  rw [lintegral_prod _ hmeas.aemeasurable]
  set c : ℝ≥0∞ := ENNReal.ofReal (2 ^ r) + ENNReal.ofReal M *
    (ENNReal.ofReal (1 ^ Module.finrank ℝ E * u1Vs s 1 ^ r) * u1J μ s r) with hc
  have hJ := u1J_lt_top μ hs hr hrs
  have hcfin : c ≠ ⊤ := by
    rw [hc]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ.ne)
  have hinner : ∀ x : E, ∫⁻ y, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖ ^ r) ∂μ' ≤ c := by
    intro x
    have hpt : ∀ y : E, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖ ^ r)
        ≤ ENNReal.ofReal (2 ^ r) + (ball x 1).indicator
            (fun y => ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r)) y := by
      intro y
      by_cases hy : y ∈ ball x 1
      · rw [indicator_of_mem hy]
        exact le_add_self
      · rw [indicator_of_notMem hy, add_zero]
        have h1 : 1 ≤ ‖x - y‖ := by
          rw [mem_ball, dist_comm, dist_eq_norm] at hy; exact not_lt.mp hy
        have h2 := u1Vs_le_two hs h1
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow (by linarith [u1Vs_ge_one (s := s) (norm_nonneg (x - y))]) h2 hr.le
    calc ∫⁻ y, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖ ^ r) ∂μ'
        ≤ ∫⁻ y, (ENNReal.ofReal (2 ^ r) + (ball x 1).indicator
            (fun y => ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r)) y) ∂μ' := lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ r) + ∫⁻ y in ball x 1, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂μ' := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_indicator measurableSet_ball]
      _ ≤ c := by
          rw [hc]
          gcongr
          exact u1_lintegral_Vs_shift_meas μ hs hr μ' hle x one_pos
  refine ne_top_of_le_ne_top hcfin ?_
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖ ^ r) ∂μ' ∂μ'
      ≤ ∫⁻ x, c ∂μ' := lintegral_mono hinner
    _ = c := by rw [lintegral_const, measure_univ, mul_one]


lemma u1_integrable_cut {s : ℝ} (hs : 0 ≤ s) (hsd : s < (Module.finrank ℝ E : ℝ))
    (f : E × E → ℝ) (hf : AEStronglyMeasurable f (μ.prod μ)) (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hbd : ∀ᵐ q ∂(μ.prod μ), |f q| ≤ B * u1Vs s ‖q.1 - q.2‖) :
    Integrable ((closedBall (0:E) R ×ˢ closedBall (0:E) R).indicator f) (μ.prod μ) := by
  set S : Set (E × E) := closedBall (0:E) R ×ˢ closedBall (0:E) R with hSdef
  have hS : MeasurableSet S := measurableSet_closedBall.prod measurableSet_closedBall
  have hJ := u1J_lt_top μ hs one_pos (by simpa using hsd)
  have hVm : Measurable (fun p : E × E => u1Vs s ‖p.1 - p.2‖) :=
    (u1Vs_measurable (E := E) s).comp (measurable_fst.sub measurable_snd)
  set g : E × E → ℝ := S.indicator (fun q => B * u1Vs s ‖q.1 - q.2‖) with hg
  have hgm : Measurable g := (measurable_const.mul hVm).indicator hS
  have hg0 : ∀ q, 0 ≤ g q := fun q => by
    simp only [hg]
    by_cases hq : q ∈ S
    · rw [indicator_of_mem hq]
      exact mul_nonneg hB (by linarith [u1Vs_ge_one (s := s) (norm_nonneg (q.1 - q.2))])
    · rw [indicator_of_notMem hq]
  have hgint : Integrable g (μ.prod μ) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
    have hfun : ∀ q, ENNReal.ofReal (g q) = S.indicator
        (fun q => ENNReal.ofReal B * ENNReal.ofReal (u1Vs s ‖q.1 - q.2‖)) q := by
      intro q
      by_cases hq : q ∈ S
      · simp [hg, indicator_of_mem hq, ENNReal.ofReal_mul hB]
      · simp [hg, indicator_of_notMem hq]
    simp_rw [hfun]
    rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hVm' : Measurable (fun p : E × E => ENNReal.ofReal (u1Vs s ‖p.1 - p.2‖)) :=
      ENNReal.measurable_ofReal.comp hVm
    rw [hSdef, ← Measure.prod_restrict, lintegral_prod _ hVm'.aemeasurable]
    set c1 : ℝ≥0∞ := ENNReal.ofReal ((2 * R + 1) ^ Module.finrank ℝ E * u1Vs s (2 * R + 1))
      * u1J μ s 1 with hc1
    have hc1fin : c1 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ.ne
    have hinner : ∀ x ∈ closedBall (0:E) R,
        ∫⁻ y in closedBall (0:E) R, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖) ∂μ ≤ c1 := by
      intro x hx
      have hsub : closedBall (0:E) R ⊆ ball x (2 * R + 1) := by
        intro y hy
        simp only [mem_closedBall, dist_zero_right] at hx hy
        rw [mem_ball, dist_eq_norm]
        calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
          _ < 2 * R + 1 := by linarith
      calc ∫⁻ y in closedBall (0:E) R, ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖) ∂μ
          ≤ ∫⁻ y in ball x (2 * R + 1), ENNReal.ofReal (u1Vs s ‖x - y‖) ∂μ :=
            lintegral_mono_set hsub
        _ ≤ c1 := by
            have := u1_lintegral_Vs_shift μ hs one_pos x (a := 2 * R + 1) (by linarith)
            simpa [Real.rpow_one] using this
    calc ∫⁻ x in closedBall (0:E) R, ∫⁻ y in closedBall (0:E) R,
          ENNReal.ofReal (u1Vs s ‖(x, y).1 - (x, y).2‖) ∂μ ∂μ
        ≤ ∫⁻ x in closedBall (0:E) R, c1 ∂μ := setLIntegral_mono' measurableSet_closedBall hinner
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top hc1fin.lt_top measure_closedBall_lt_top
  refine hgint.mono' (hf.indicator hS) ?_
  filter_upwards [hbd] with q hq
  by_cases hqS : q ∈ S
  · simp [hg, indicator_of_mem hqS, hq]
  · simp [hg, indicator_of_notMem hqS]

end HRS.Whole.U1
