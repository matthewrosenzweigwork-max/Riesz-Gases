/-
# HRS.MD.DOMDct — packet DOM (dominated convergence and assembly)

Squeeze/dominated-convergence lemma for functions bounded by `K Pw⁸` and vanishing off the shell `Near ε_n`,
and the assembly of `normal_form_domain_proof`.
-/
import HRS.MD.DOMLeib2
import HRS.MD.DOMSpec

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem domp_measurableSet_Near (ε : ℝ) : MeasurableSet {X : Config d N | Near ε X} := by
  have : {X : Config d N | Near ε X} =
      ⋃ a : Fin N, ⋃ b : Fin N, ⋃ (_ : a ≠ b), {X | sT (X a - X b) ≤ 2 * ε} := by
    ext X; simp [Near]
  rw [this]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => ?_
  exact (isClosed_le (domp_continuous_sT.comp ((continuous_apply a).sub (continuous_apply b)))
    continuous_const).measurableSet

theorem domp_eventually_not_near {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {X : Config d N}
    (hX : X ∉ collisionSet d N) : ∀ᶠ n in atTop, ¬ Near (ε n) X := by
  have hne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have key : ∀ a b : Fin N, ∀ᶠ n in atTop, a ≠ b → 2 * ε n < sT (X a - X b) := by
    intro a b
    by_cases hab : a = b
    · exact Eventually.of_forall fun n h => absurd hab h
    · have hpos : 0 < sT (X a - X b) := domp_sT_pos (sub_ne_zero.2 (hne a b hab))
      have h2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 (2 * 0)) := hε.const_mul 2
      rw [mul_zero] at h2
      filter_upwards [h2.eventually (gt_mem_nhds hpos)] with n hn _ using hn
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => key a b] with n hn
  rintro ⟨a, b, hab, h⟩
  linarith [hn a b hab]

/-- The squeeze: a function bounded by `K Pw⁸` and vanishing off `Near (ε n)` has `∫⁻ → 0`. -/
theorem domp_tendsto_lintegral {μ : Measure (Config d N)}
    (hint : Integrable (fun X : Config d N => Pw s X ^ 8) μ) (hnc : ∀ᵐ X ∂μ, X ∉ collisionSet d N)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {K : ℝ} (hK : 0 ≤ K)
    (w : ℕ → Config d N → ℝ≥0∞)
    (hw : ∀ n, ∀ᵐ X ∂μ, w n X ≤ ENNReal.ofReal (K * Pw s X ^ 8) ∧ (¬ Near (ε n) X → w n X = 0)) :
    Tendsto (fun n => ∫⁻ X, w n X ∂μ) atTop (𝓝 0) := by
  set b : Config d N → ℝ≥0∞ := fun X => ENNReal.ofReal (K * Pw s X ^ 8) with hb
  set F : ℕ → Config d N → ℝ≥0∞ := fun n => {X | Near (ε n) X}.indicator b with hF
  have hbm : Measurable b := by
    have h1 : Measurable (fun X : Config d N => K * Pw s X ^ 8) :=
      (domp_measurable_Pw.pow_const 8).const_mul K
    exact ENNReal.measurable_ofReal.comp h1
  have hFm : ∀ n, Measurable (F n) := fun n => hbm.indicator (domp_measurableSet_Near (ε n))
  have hfin : ∫⁻ X, b X ∂μ ≠ ∞ := (hint.const_mul K).lintegral_lt_top.ne
  have hlim : Tendsto (fun n => ∫⁻ X, F n X ∂μ) atTop (𝓝 (∫⁻ X, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence b hFm (fun n => Eventually.of_forall fun X => ?_)
      hfin ?_
    · exact Set.indicator_le_self _ _ X
    · filter_upwards [hnc] with X hX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [domp_eventually_not_near hε hX] with n hn
      simp [hF, Set.indicator_of_notMem, hn]
  rw [lintegral_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) fun n => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hw n] with X ⟨h1, h2⟩
  by_cases hN : Near (ε n) X
  · simpa [hF, Set.indicator_of_mem, hN] using h1
  · simp [hF, h2 hN]

/-- eLpNorm version. -/
theorem domp_tendsto_eLpNorm {μ : Measure (Config d N)}
    (hint : Integrable (fun X : Config d N => Pw s X ^ 8) μ) (hnc : ∀ᵐ X ∂μ, X ∉ collisionSet d N)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {C : ℝ}
    (h : ℕ → Config d N → ℝ) (hm : ∀ n, AEStronglyMeasurable (h n) μ)
    (hh : ∀ n, ∀ᵐ X ∂μ, ‖h n X‖ ≤ C * Pw s X ^ 4 ∧ (¬ Near (ε n) X → h n X = 0)) :
    Tendsto (fun n => eLpNorm (h n) 2 μ) atTop (𝓝 0) := by
  have hC : 0 ≤ C ^ 2 := sq_nonneg C
  have hL := domp_tendsto_lintegral hint hnc hε hC (fun n X => ‖h n X‖ₑ ^ 2) (fun n => by
    filter_upwards [hh n] with X ⟨h1, h2⟩
    refine ⟨?_, fun hN => by simp [h2 hN]⟩
    have h3 : ‖h n X‖ₑ ≤ ENNReal.ofReal (C * Pw s X ^ 4) := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h1
    calc ‖h n X‖ₑ ^ 2 ≤ ENNReal.ofReal (C * Pw s X ^ 4) ^ 2 := pow_le_pow_left' h3 2
      _ = ENNReal.ofReal ((C * Pw s X ^ 4) ^ 2) := by
          rw [ENNReal.ofReal_pow (le_trans (norm_nonneg _) h1)]
      _ = ENNReal.ofReal (C ^ 2 * Pw s X ^ 8) := by congr 1; ring)
  have e : ∀ n, eLpNorm (h n) 2 μ = (∫⁻ X, ‖h n X‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hm n)]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun X => ?_
    rw [ENNReal.rpow_two]
  simp only [e]
  have h2 : Tendsto (fun n => (∫⁻ X, ‖h n X‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hL
  rwa [ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] at h2

end HRS.MD.DOMProof
