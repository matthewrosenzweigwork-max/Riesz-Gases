import Mathlib

/-!
# MOVE Aux1: generic duality lemmas for `movT_lp_lsc`

Mathlib-only.  `move_approx_cont`: bounded nonnegative Borel functions are a.e. limits of uniformly bounded nonnegative
continuous functions (a.e. for any finite measure on a compact metric space).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS

theorem move_clip_dist {a ψ B : ℝ} (h0 : 0 ≤ ψ) (hB : ψ ≤ B) :
    |ψ - max 0 (min B a)| ≤ |ψ - a| := by
  simp only [abs_le]
  rcases le_total a B with h | h
  · rw [min_eq_right h]
    rcases le_total 0 a with h' | h'
    · rw [max_eq_right h']; constructor <;> linarith [abs_nonneg (ψ - a), neg_abs_le (ψ - a), le_abs_self (ψ - a)]
    · rw [max_eq_left h']
      have := neg_abs_le (ψ - a); have := le_abs_self (ψ - a)
      constructor <;> linarith [abs_nonneg (ψ - a)]
  · rw [min_eq_left h, max_eq_right (by linarith)]
    have := neg_abs_le (ψ - a); have := le_abs_self (ψ - a)
    constructor <;> linarith [abs_nonneg (ψ - a)]

theorem move_approx_cont {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] {ψ : α → ℝ} (hψ : Measurable ψ) {B : ℝ}
    (h0 : ∀ x, 0 ≤ ψ x) (hB : ∀ x, ψ x ≤ B) :
    ∃ g : ℕ → α → ℝ, (∀ n, Continuous (g n)) ∧ (∀ n x, 0 ≤ g n x ∧ g n x ≤ B) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (ψ x)) := by
  have hmem : MemLp ψ 1 μ := by
    refine MemLp.of_bound hψ.aestronglyMeasurable B (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hB x
  have hex : ∀ n : ℕ, ∃ g : BoundedContinuousFunction α ℝ,
      eLpNorm (ψ - (g : α → ℝ)) 1 μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧ MemLp g 1 μ := fun n =>
    hmem.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
      (by simp [Nat.cast_add_one_pos])
  choose g hg using hex
  set c : ℕ → α → ℝ := fun n x => max 0 (min B (g n x)) with hc
  have hcc : ∀ n, Continuous (c n) := fun n =>
    continuous_const.max (continuous_const.min (g n).continuous)
  have hcb : ∀ n x, 0 ≤ c n x ∧ c n x ≤ B := by
    intro n x
    refine ⟨le_max_left _ _, max_le ((h0 x).trans (hB x)) (min_le_left _ _)⟩
  have hnorm : ∀ n, eLpNorm (ψ - c n) 1 μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have : eLpNorm (ψ - c n) 1 μ ≤ eLpNorm (ψ - (g n : α → ℝ)) 1 μ := by
      refine eLpNorm_mono (hψ.aestronglyMeasurable.sub (hcc n).aestronglyMeasurable) fun x => ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs, hc]
      exact move_clip_dist (h0 x) (hB x)
    exact this.trans (hg n).1
  have hlim : Tendsto (fun n => eLpNorm (ψ - c n) 1 μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => bot_le) hnorm
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (E := ℝ) (f := c) (g := ψ) (l := atTop)
    one_ne_zero (by simpa [eLpNorm_sub_comm] using hlim)
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨fun n => c (ns n), fun n => hcc _, fun n x => hcb _ _, hae⟩


theorem move_dual_ext {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {ν Q : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure Q] {q : ℝ} (hq : 0 < q)
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hφ : ∀ φ : α → ℝ, Continuous φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ A * (∫⁻ x, ENNReal.ofReal (φ x) ^ q ∂Q) ^ (1 / q))
    {ψ : α → ℝ} (hψ : Measurable ψ) {B : ℝ} (h0 : ∀ x, 0 ≤ ψ x) (hB : ∀ x, ψ x ≤ B) :
    ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν ≤ A * (∫⁻ x, ENNReal.ofReal (ψ x) ^ q ∂Q) ^ (1 / q) := by
  obtain ⟨g, hgc, hgb, hgl⟩ := move_approx_cont (ν + Q) hψ h0 hB
  rw [ae_add_measure_iff] at hgl
  obtain ⟨hglν, hglQ⟩ := hgl
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (g n x) := fun n =>
    ENNReal.measurable_ofReal.comp (hgc n).measurable
  have h1 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂ν) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal B) hmeas
      (fun n => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hgb n x).2) ?_ ?_
    · rw [lintegral_const]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)).ne
    · filter_upwards [hglν] with x hx
      exact (ENNReal.continuous_ofReal.tendsto _).comp hx
  have h2 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ^ q ∂Q) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (ψ x) ^ q ∂Q)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal B ^ q)
      (fun n => (hmeas n).pow_const q)
      (fun n => Eventually.of_forall fun x =>
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hgb n x).2) hq.le) ?_ ?_
    · rw [lintegral_const]
      exact (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
        (measure_lt_top _ _)).ne
    · filter_upwards [hglQ] with x hx
      exact ((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp
        ((ENNReal.continuous_ofReal.tendsto _).comp hx)
  have h3 : Tendsto (fun n => A * (∫⁻ x, ENNReal.ofReal (g n x) ^ q ∂Q) ^ (1 / q)) atTop
      (𝓝 (A * (∫⁻ x, ENNReal.ofReal (ψ x) ^ q ∂Q) ^ (1 / q))) :=
    ENNReal.Tendsto.const_mul (((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto _).comp h2)
      (Or.inr hA)
  exact le_of_tendsto_of_tendsto' h1 h3 fun n => hφ _ (hgc n) fun x => (hgb n x).1

end HRS

end
