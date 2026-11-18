import HRS.MS.SA16RHeat8

/-!
# S.A.16 (SA16R) Heat9: translation continuity in `L^p` and the approximate identity

`sa16r_T u p z = ∫ |u(x-z) - u(x)|^p dx`; `sa16r_T_tendsto`: `T → 0` at `z = 0` for `u` continuous with compact support;
`sa16r_T_le`: the global bound `T z ≤ 2^p ∫ |u|^p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat9
variable {d : ℕ}

def sa16r_T (u : Euc d → ℝ) (p : ℝ) (z : Euc d) : ℝ≥0∞ := ∫⁻ x, ‖u (x - z) - u x‖ₑ ^ p

lemma sa16r_cc_support {u : Euc d → ℝ} (hs : HasCompactSupport u) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < ‖x‖ → u x = 0 := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall (0 : Euc d)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  by_contra hne
  have : x ∈ tsupport u := subset_closure (Function.mem_support.2 hne)
  have := mem_closedBall_zero_iff.1 (hR this)
  exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left R 0) hx)) (lt_irrefl _)

lemma sa16r_lint_u_lt {u : Euc d → ℝ} (hu : Continuous u) (hs : HasCompactSupport u) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖u x‖ₑ ^ p < ⊤ := by
  obtain ⟨R, hR0, hR⟩ := sa16r_cc_support hs
  obtain ⟨B, hB⟩ := hu.bounded_above_of_compact_support hs
  have hle : ∀ x, ‖u x‖ₑ ^ p ≤ (closedBall (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal B ^ p) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : Euc d) R
    · rw [indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB x)
    · rw [indicator_of_notMem hx]
      have : u x = 0 := hR x (by simpa using hx)
      simp [this, ENNReal.zero_rpow_of_pos hp]
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_indicator_const measurableSet_closedBall]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
    measure_closedBall_lt_top

lemma sa16r_T_le {u : Euc d → ℝ} (hu : Continuous u) {p : ℝ} (hp : 1 ≤ p) (z : Euc d) :
    sa16r_T u p z ≤ 2 ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hp0 : 0 ≤ p - 1 := by linarith
  unfold sa16r_T
  have h1 : ∀ x, ‖u (x - z) - u x‖ₑ ^ p ≤ 2 ^ (p - 1) * (‖u (x - z)‖ₑ ^ p + ‖u x‖ₑ ^ p) := by
    intro x
    refine le_trans (ENNReal.rpow_le_rpow enorm_sub_le (by linarith)) ?_
    exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
  have hmeasf : Measurable (fun x => ‖u (x - z)‖ₑ ^ p) :=
    (hu.comp (continuous_id.sub continuous_const)).measurable.enorm.pow_const p
  calc ∫⁻ x, ‖u (x - z) - u x‖ₑ ^ p
      ≤ ∫⁻ x, 2 ^ (p - 1) * (‖u (x - z)‖ₑ ^ p + ‖u x‖ₑ ^ p) := lintegral_mono h1
    _ = 2 ^ (p - 1) * ∫⁻ x, (‖u (x - z)‖ₑ ^ p + ‖u x‖ₑ ^ p) := lintegral_const_mul' _ _ (by simp)
    _ = 2 ^ (p - 1) * ((∫⁻ x, ‖u (x - z)‖ₑ ^ p) + ∫⁻ x, ‖u x‖ₑ ^ p) := by
        rw [lintegral_add_left hmeasf]
    _ = 2 ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
        rw [lintegral_sub_right_eq_self (fun x => ‖u x‖ₑ ^ p) z, ← two_mul, ← mul_assoc]
        congr 1
        have := ENNReal.rpow_add_of_nonneg (x := (2 : ℝ≥0∞)) (p - 1) 1 hp0 zero_le_one
        rw [sub_add_cancel, ENNReal.rpow_one] at this
        exact this.symm

lemma sa16r_T_tendsto {u : Euc d → ℝ} (hu : Continuous u) (hs : HasCompactSupport u) {p : ℝ} (hp : 0 < p) :
    Tendsto (sa16r_T u p) (𝓝 0) (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := sa16r_cc_support hs
  obtain ⟨B, hB⟩ := hu.bounded_above_of_compact_support hs
  have hB' : ∀ y, ‖u y‖ ≤ B := hB
  set bd : Euc d → ℝ≥0∞ := (closedBall (0 : Euc d) (R + 1)).indicator
    (fun _ => ENNReal.ofReal (2 * B) ^ p) with hbd
  have hbdint : ∫⁻ x, bd x ≠ ⊤ := by
    rw [hbd, lintegral_indicator_const measurableSet_closedBall]
    exact (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      measure_closedBall_lt_top).ne
  have hmeas : ∀ z : Euc d, Measurable (fun x => ‖u (x - z) - u x‖ₑ ^ p) := by
    intro z
    exact ((hu.comp (continuous_id.sub continuous_const)).sub hu).measurable.enorm.pow_const _
  have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 (0 : Euc d))
    (F := fun z x => ‖u (x - z) - u x‖ₑ ^ p) (f := fun _ => (0 : ℝ≥0∞)) bd
    (Eventually.of_forall fun z => hmeas z) ?_ hbdint ?_
  · have h0 : ∫⁻ _ : Euc d, (0 : ℝ≥0∞) = 0 := lintegral_zero
    rw [h0] at this
    exact this
  · have hz : ∀ᶠ z in 𝓝 (0 : Euc d), ‖z‖ < 1 := by
      have : Continuous (fun z : Euc d => ‖z‖) := continuous_norm
      exact (this.tendsto 0).eventually (Iio_mem_nhds (by simp))
    filter_upwards [hz] with z hz1
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Euc d) (R + 1)
    · rw [hbd, indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
      linarith [hB' (x - z), hB' x]
    · rw [hbd, indicator_of_notMem hx]
      have hx' : R + 1 < ‖x‖ := by simpa using hx
      have h1 : u x = 0 := hR x (by linarith)
      have h2 : u (x - z) = 0 := hR _ (by
        have := norm_sub_norm_le x z
        have := (norm_sub_rev x z ▸ norm_sub_norm_le x z : ‖x‖ - ‖z‖ ≤ ‖x - z‖)
        linarith)
      simp [h1, h2, ENNReal.zero_rpow_of_pos hp]
  · refine Eventually.of_forall fun x => ?_
    have h1 : Tendsto (fun z : Euc d => u (x - z)) (𝓝 0) (𝓝 (u x)) := by
      have : Continuous (fun z : Euc d => u (x - z)) := hu.comp (continuous_const.sub continuous_id)
      simpa using this.tendsto 0
    have h2 : Tendsto (fun z : Euc d => ‖u (x - z) - u x‖ₑ) (𝓝 0) (𝓝 0) := by
      have := (h1.sub_const (u x)).enorm
      simpa using this
    have := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
    simp only [Function.comp_def, ENNReal.zero_rpow_of_pos hp] at this
    exact this

end Heat9

end HRS.Whole.AppendixA.Phase2SA16R
