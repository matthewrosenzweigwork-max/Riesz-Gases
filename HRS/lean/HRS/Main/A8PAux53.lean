import HRS.Main.A8PAux52

/-!
# Packet A8P, part 53: the zero set of a real semimartingale with nondegenerate noise is `dt`-null
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

section ZeroNull

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ}

theorem a8p_zero_null (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T)
    (σ : ι → ℝ) (hν : 0 < ∑ k, σ k ^ 2) (X : ℝ≥0 → Ω → ℝ) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0))
    (b : ℝ≥0 → Ω → ℝ) (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W t ω k - W 0 ω k) • σ k) :
    ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω = 0} = 0 := by
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by simp only [hεn]; positivity
  choose M hMm hMV hcont hineq using fun n : ℕ =>
    a8p_ito_scalar' hW hT (hεpos n) σ X hX₀ b hb hbint hX
  set ν : ℝ := (1 / 2) * ∑ k, σ k ^ 2 with hνdef
  have hν0 : 0 < ν := by simp only [hνdef]; positivity
  -- summability of the second moments
  have hsq : ∫⁻ ω, ∑' n, ‖εn n * M n ω‖ₑ ^ 2 ∂P ≠ ∞ := by
    rw [lintegral_tsum (fun n => ((hMm n).const_mul (εn n)).enorm.pow_const 2 |>.aemeasurable)]
    have h1 : ∀ n, ∫⁻ ω, ‖εn n * M n ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (εn n ^ 2) * (ENNReal.ofReal T * ENNReal.ofReal (∑ k, σ k ^ 2)) := by
      intro n
      calc ∫⁻ ω, ‖εn n * M n ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (εn n ^ 2) * ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂P := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun ω => ?_
            rw [enorm_mul, mul_pow, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hεpos n).le,
              ENNReal.ofReal_pow (hεpos n).le]
        _ ≤ _ := mul_le_mul' le_rfl (hMV n)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _)]
    · exact ENNReal.ofReal_ne_top
    · have h0 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
        simpa [Nat.cast_add, Nat.cast_one] using this
      refine h0.congr fun n => ?_
      simp only [hεn, one_div, inv_pow]
  have hae : ∀ᵐ ω ∂P, ∑' n, ‖εn n * M n ω‖ₑ ^ 2 ≠ ∞ := by
    have hm : AEMeasurable (fun ω => ∑' n, ‖εn n * M n ω‖ₑ ^ 2) P :=
      (Measurable.ennreal_tsum fun n => ((hMm n).const_mul (εn n)).enorm.pow_const 2).aemeasurable
    exact ae_lt_top' hm hsq |>.mono fun ω h => h.ne
  have hallb := ae_all_iff.2 hineq
  have hallc := hcont 0
  filter_upwards [hae, hallb, hallc, hbint, hX] with ω h1 h2 h3 h4 h5
  -- the quantities
  set R : ℝ := |X (Real.toNNReal T) ω - X 0 ω| + ∫ s in Set.Icc (0 : ℝ) T, |b (Real.toNNReal s) ω|
    with hR
  have hbound : ∀ n, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω = 0} ≤
      ENNReal.ofReal (8 * εn n / ν * (R + |M n ω|)) := by
    intro n
    have h6 := a8p_small_set hT h3 (hεpos n)
    refine h6.trans (ENNReal.ofReal_le_ofReal ?_)
    have h7 := h2 n
    have h8 : ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' (εn n) (X (Real.toNNReal s) ω) ≤
        (R + |M n ω|) / ν := by
      rw [le_div_iff₀ hν0, mul_comm]
      simpa [hR, hνdef, add_assoc] using h7
    calc 8 * εn n * ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' (εn n) (X (Real.toNNReal s) ω)
        ≤ 8 * εn n * ((R + |M n ω|) / ν) :=
          mul_le_mul_of_nonneg_left h8 (by have := hεpos n; positivity)
      _ = 8 * εn n / ν * (R + |M n ω|) := by ring
  -- the limit
  have hεt : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hMt : Tendsto (fun n => εn n * |M n ω|) atTop (𝓝 0) := by
    have h9 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h1
    have h10 : Tendsto (fun n => ENNReal.ofReal ((εn n * |M n ω|) ^ 2)) atTop (𝓝 0) := by
      refine h9.congr fun n => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hεpos n).le]
    have h11 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h10
    have h11' : Tendsto (fun n => (εn n * |M n ω|) ^ 2) atTop (𝓝 0) := by
      refine h11.congr fun n => ?_
      simp [ENNReal.toReal_ofReal (sq_nonneg _)]
    have h12 := (Real.continuous_sqrt.tendsto 0).comp h11'
    simp only [Real.sqrt_zero] at h12
    refine h12.congr fun n => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (mul_nonneg (hεpos n).le (abs_nonneg _))
  have hu : Tendsto (fun n => 8 * εn n / ν * (R + |M n ω|)) atTop (𝓝 0) := by
    have h13 := (hεt.mul_const R).add hMt
    have h14 := h13.const_mul (8 / ν)
    simp only [zero_mul, add_zero, mul_zero] at h14
    refine h14.congr fun n => ?_
    ring
  have hlim := ENNReal.tendsto_ofReal hu
  rw [ENNReal.ofReal_zero] at hlim
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

end ZeroNull

end HRS.Main.A8P
