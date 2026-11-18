import HRS.MS.S82P2Sum2
import HRS.MS.CritForceMom5

/-!
# S8.2 (S82P2): simplified second moment of a centered sum (UNCOMPILED DRAFT)
Combines `s82p2_centered_sum_sq` with Cauchy-Schwarz and the uniform bound on `conv q mu`
(`small_row`), giving `∫⁻ S² ≤ ofReal (Cs * N * ∫ ψ²)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- A bound `q(w) ≤ K1 · (1 + min(1,|w|)^{-s})` for `w ≠ 0` (adapted from `s82p_q_le`). -/
lemma s82p2_q_le {d : ℕ} {q : Euc d → ℝ} (hq : ShortRangePole d q) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ w : Euc d, w ≠ 0 →
      q w ≤ K1 * (1 + (min 1 ‖w‖) ^ (-criticalS d)) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  obtain ⟨r1, c1, C1, hr1p, hc1, hfar⟩ := hq.far
  have hcomp : IsCompact {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} := by
    have : {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} =
        Metric.closedBall (0 : Euc d) r1 ∩ {w | r0 ≤ ‖w‖} := by
      ext w; simp [and_comm]
    rw [this]
    exact (isCompact_closedBall 0 r1).inter_right (isClosed_le continuous_const continuous_norm)
  have hcont : ContinuousOn q {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} :=
    hq.smooth.continuousOn.mono fun w hw => by
      have : 0 < ‖w‖ := lt_of_lt_of_le hr0 hw.1
      exact norm_pos_iff.1 this
  obtain ⟨Cb, hCb⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C0 0 + max C1 0 + max Cb 0, by positivity, ?_⟩
  intro w hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hP : 1 ≤ 1 + (min 1 ‖w‖) ^ (-criticalS d) := by
    have : 0 ≤ (min 1 ‖w‖) ^ (-criticalS d) :=
      Real.rpow_nonneg (le_min zero_le_one hwpos.le) _
    linarith
  have hA : 0 ≤ max C0 0 := le_max_right _ _
  have hB : 0 ≤ max C1 0 := le_max_right _ _
  have hC : 0 ≤ max Cb 0 := le_max_right _ _
  by_cases h0 : ‖w‖ ≤ r0
  · have h1 := (hnear w hwpos h0).2
    have hm : min 1 ‖w‖ = ‖w‖ := min_eq_right (h0.trans hr1)
    rw [hm]
    have h2 : 0 ≤ ‖w‖ ^ (-criticalS d) := Real.rpow_nonneg hwpos.le _
    calc q w ≤ C0 * ‖w‖ ^ (-criticalS d) := h1
      _ ≤ max C0 0 * ‖w‖ ^ (-criticalS d) := by gcongr; exact le_max_left _ _
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * (1 + ‖w‖ ^ (-criticalS d)) := by
          have : 0 ≤ ‖w‖ ^ (-criticalS d) := h2
          nlinarith
  · push Not at h0
    have hq0 := hq.nonneg w
    have hb : q w ≤ max C1 0 + max Cb 0 := by
      by_cases h1 : r1 ≤ ‖w‖
      · have := hfar w h1
        have he : Real.exp (-c1 * ‖w‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖w‖]
        have : C1 * Real.exp (-c1 * ‖w‖ ^ 2) ≤ max C1 0 := by
          have hep := Real.exp_pos (-c1 * ‖w‖ ^ 2)
          rcases le_total C1 0 with hC1 | hC1
          · nlinarith [le_max_right C1 0]
          · calc C1 * Real.exp (-c1 * ‖w‖ ^ 2) ≤ C1 * 1 := by gcongr
              _ = C1 := mul_one _
              _ ≤ max C1 0 := le_max_left _ _
        linarith
      · push Not at h1
        have := hCb w ⟨h0.le, h1.le⟩
        rw [Real.norm_eq_abs] at this
        have := (le_abs_self (q w)).trans this
        have := this.trans (le_max_left Cb 0)
        linarith
    calc q w ≤ max C1 0 + max Cb 0 := hb
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * 1 := by linarith
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * (1 + (min 1 ‖w‖) ^ (-criticalS d)) := by
          gcongr

/-- Cauchy-Schwarz for nonnegative measurable functions. -/
lemma s82p2_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have hfL : MemLp f (ENNReal.ofReal 2) μ := by
    rw [h2]; exact (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 hf
  have hgL : MemLp g (ENNReal.ofReal 2) μ := by
    rw [h2]; exact (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hg
  have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) hfL hgL
  simpa [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using this

/-- `q(· - x)` is integrable against the thermal measure, and its integral is `conv q mu x`. -/
lemma s82p2_mu_singleton {d : ℕ} (hd : 2 ≤ d) (rho : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.withDensityReal rho {x} = 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h0 : (volume : Measure (Euc d)) {x} = 0 := measure_singleton x
  exact (withDensity_absolutelyContinuous _ _) h0

/-- `q(· - x)` is integrable against the thermal measure. -/
lemma s82p2_q_integrable {d : ℕ} (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q)
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (rho : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    (x : Euc d) :
    Integrable (fun z => q (z - x)) (HRS.Whole.withDensityReal rho) := by
  obtain ⟨K1, hK1, hqK⟩ := s82p2_q_le hq
  have hE2 := HRS.MS.S82N.s82n_E2 hd 0 G c 1 le_rfl hG.le hc one_pos le_rfl rho hρ hρG x
  have hm : Measurable (fun z => q (z - x)) := hq.measurable.comp (measurable_id.sub_const x)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => hq.nonneg _)]
  have hae : ∀ᵐ z ∂HRS.Whole.withDensityReal rho, z ≠ x := by
    have := s82p2_mu_singleton hd rho x
    rw [ae_iff]
    simpa using this
  calc ∫⁻ z, ENNReal.ofReal (q (z - x)) ∂HRS.Whole.withDensityReal rho
      ≤ ∫⁻ z, ENNReal.ofReal K1 * ENNReal.ofReal (jbracket z ^ (0 : ℝ) *
          ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
            HRS.MS.S82N.s82n_pole x z)) ∂HRS.Whole.withDensityReal rho := by
        refine lintegral_mono_ae (hae.mono fun z hz => ?_)
        rw [← ENNReal.ofReal_mul hK1]
        apply ENNReal.ofReal_le_ofReal
        have h1 := hqK (z - x) (sub_ne_zero.2 hz)
        have hr0 : 0 ≤ HRS.MS.S82N.s82n_smallRadius x z :=
          le_min zero_le_one (norm_nonneg _)
        have hpole : 0 ≤ HRS.MS.S82N.s82n_pole x z := by
          unfold HRS.MS.S82N.s82n_pole
          have := Real.rpow_nonneg hr0 (-HRS.MS.S82N.s82n_critS d)
          linarith
        have hA : 1 ≤ 1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d) := by
          have := Real.rpow_nonneg hr0 (1 - HRS.MS.S82N.s82n_critS d)
          linarith
        have hz' : (min 1 ‖z - x‖) = HRS.MS.S82N.s82n_smallRadius x z := by
          unfold HRS.MS.S82N.s82n_smallRadius
          rw [norm_sub_rev]
        rw [hz'] at h1
        have e : (1 + HRS.MS.S82N.s82n_smallRadius x z ^ (-criticalS d)) =
            HRS.MS.S82N.s82n_pole x z := rfl
        rw [e] at h1
        rw [Real.rpow_zero, one_mul]
        calc q (z - x) ≤ K1 * HRS.MS.S82N.s82n_pole x z := h1
          _ ≤ K1 * ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
              HRS.MS.S82N.s82n_pole x z) := by
            apply mul_le_mul_of_nonneg_left _ hK1
            nlinarith
    _ = ENNReal.ofReal K1 * ∫⁻ z, ENNReal.ofReal (jbracket z ^ (0 : ℝ) *
          ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
            HRS.MS.S82N.s82n_pole x z)) ∂HRS.Whole.withDensityReal rho :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hE2 ENNReal.ofReal_lt_top)

/-- Uniform bound on the mass of `q (· - x)`: `∫ q(z-x) dmu ≤ 1/(1000 β)`. -/
lemma s82p2_q_mass {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta) (x : Euc d) :
    ∫ z, q (z - x) ∂HRS.Whole.withDensityReal rho ≤ 1 / (1000 * beta) := by
  have h1 := hW.small_row x
  have e : ∫ z, q (z - x) ∂HRS.Whole.withDensityReal rho =
      HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x := by
    unfold HRS.Whole.convMeasure
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show q (z - x) = q (x - z)
    rw [← hW.short.even (x - z), neg_sub]
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

end HRS.MS.S82P2
