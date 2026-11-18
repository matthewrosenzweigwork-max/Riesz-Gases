import HRS.MS.ShiftFldAux21

/-!
# S79P: calculus of `L²(μ)`-valued paths from pointwise information (dominated convergence)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21
open HRS (Euc)

variable {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν]

theorem s79g_dct_sq (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) ν) {l : Filter ℝ}
    [l.IsCountablyGenerated] {q : ℝ → Euc d → ℝ} {B : ℝ}
    (hmeas : ∀ᶠ r in l, AEStronglyMeasurable (q r) ν)
    (hb : ∀ᶠ r in l, ∀ x, |q r x| ≤ B * (1 + ‖x‖))
    (hlim : ∀ x, Tendsto (fun r => q r x) l (𝓝 0)) :
    Tendsto (fun r => ∫ x, (q r x) ^ 2 ∂ν) l (𝓝 0) := by
  have hB : Integrable (fun x : Euc d => 2 * B ^ 2 + 2 * B ^ 2 * ‖x‖ ^ 2) ν :=
    (integrable_const _).add (hint2.const_mul _)
  have := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := l)
    (F := fun r x => (q r x) ^ 2) (f := fun _ => 0)
    (fun x => 2 * B ^ 2 + 2 * B ^ 2 * ‖x‖ ^ 2)
    (hmeas.mono fun r h => h.pow 2)
    (hb.mono fun r h => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      have h1 := h x
      have h0 : 0 ≤ |q r x| := abs_nonneg _
      have hn := norm_nonneg x
      calc |q r x| ^ 2 ≤ (B * (1 + ‖x‖)) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ ≤ _ := by nlinarith [sq_nonneg (B * (1 - ‖x‖)), sq_nonneg B])
    hB (Filter.Eventually.of_forall fun x => by
      have := (hlim x).pow 2
      simpa using this)
  simpa using this

theorem s79g_lp_tendsto (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) ν) {l : Filter ℝ}
    [l.IsCountablyGenerated] {F : ℝ → Lp ℝ 2 ν} {G : Lp ℝ 2 ν} {q : ℝ → Euc d → ℝ} {B : ℝ}
    (hq : ∀ᶠ r in l, (fun x => (F r : Euc d → ℝ) x - (G : Euc d → ℝ) x) =ᵐ[ν] q r)
    (hmeas : ∀ᶠ r in l, AEStronglyMeasurable (q r) ν)
    (hb : ∀ᶠ r in l, ∀ x, |q r x| ≤ B * (1 + ‖x‖))
    (hlim : ∀ x, Tendsto (fun r => q r x) l (𝓝 0)) :
    Tendsto F l (𝓝 G) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := s79g_dct_sq hint2 hmeas hb hlim
  have h2 : Tendsto (fun r => ‖F r - G‖ ^ 2) l (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [hq] with r hr
    rw [HRS.Whole.Q34.lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hr, Lp.coeFn_sub (F r) G] with x h1 h2
    rw [h2, Pi.sub_apply, h1]
  have := h2.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr fun r => ?_
  exact Real.sqrt_sq (norm_nonneg _)

theorem s79g_lp_continuousWithinAt (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) ν) {S : Set ℝ}
    {f : ℝ → Euc d → ℝ} {B : ℝ} (hc : ∀ x, ContinuousOn (fun r => f r x) S)
    (hB : ∀ r ∈ S, ∀ x, |f r x| ≤ B * (1 + ‖x‖)) {F : ℝ → Lp ℝ 2 ν}
    (hF : ∀ r ∈ S, (F r : Euc d → ℝ) =ᵐ[ν] f r) {r₀ : ℝ} (hr₀ : r₀ ∈ S) :
    ContinuousWithinAt F S r₀ := by
  refine s79g_lp_tendsto hint2 (l := 𝓝[S] r₀) (q := fun r x => f r x - f r₀ x) (B := 2 * B) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [hF r hr, hF r₀ hr₀] with x h1 h2
    rw [h1, h2]
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have h1 := (Lp.aestronglyMeasurable (F r)).congr (hF r hr)
    have h2 := (Lp.aestronglyMeasurable (F r₀)).congr (hF r₀ hr₀)
    exact h1.sub h2
  · filter_upwards [self_mem_nhdsWithin] with r hr x
    have h1 := hB r hr x
    have h2 := hB r₀ hr₀ x
    calc |f r x - f r₀ x| ≤ |f r x| + |f r₀ x| := abs_sub _ _
      _ ≤ _ := by linarith
  · intro x
    have := ((hc x) r₀ hr₀).tendsto
    have h2 := this.sub_const (f r₀ x)
    simpa using h2

theorem s79g_lp_hasDerivAt (hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) ν)
    {f D : ℝ → Euc d → ℝ} {r₀ δ0 B : ℝ} (hδ : 0 < δ0)
    (hd : ∀ x, ∀ r ∈ ball r₀ δ0, HasDerivAt (fun r' => f r' x) (D r x) r)
    (hB : ∀ r ∈ ball r₀ δ0, ∀ x, |D r x| ≤ B * (1 + ‖x‖))
    {F : ℝ → Lp ℝ 2 ν} {G : Lp ℝ 2 ν}
    (hF : ∀ r ∈ ball r₀ δ0, (F r : Euc d → ℝ) =ᵐ[ν] f r) (hG : (G : Euc d → ℝ) =ᵐ[ν] D r₀) :
    HasDerivAt F G r₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hr₀ : r₀ ∈ ball r₀ δ0 := mem_ball_self hδ
  have hball : ball r₀ δ0 ∈ 𝓝[≠] r₀ := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ)
  refine s79g_lp_tendsto hint2 (l := 𝓝[≠] r₀)
    (q := fun r x => (r - r₀)⁻¹ * (f r x - f r₀ x) - D r₀ x) (B := 2 * B) ?_ ?_ ?_ ?_
  · filter_upwards [hball] with r hr
    filter_upwards [hF r hr, hF r₀ hr₀, hG, Lp.coeFn_smul (r - r₀)⁻¹ (F r - F r₀),
      Lp.coeFn_sub (F r) (F r₀)] with x h1 h2 h3 h4 h5
    simp only [slope_def_module]
    rw [h4, Pi.smul_apply, h5, Pi.sub_apply, h1, h2, h3, smul_eq_mul]
  · filter_upwards [hball] with r hr
    have h1 := (Lp.aestronglyMeasurable (F r)).congr (hF r hr)
    have h2 := (Lp.aestronglyMeasurable (F r₀)).congr (hF r₀ hr₀)
    have h3 := (Lp.aestronglyMeasurable G).congr hG
    exact ((h1.sub h2).const_mul _).sub h3
  · filter_upwards [hball, self_mem_nhdsWithin] with r hr hne x
    have hne' : r - r₀ ≠ 0 := sub_ne_zero.2 hne
    have hmvt := (convex_ball r₀ δ0).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r' => f r' x) (f' := fun r' => D r' x) (C := B * (1 + ‖x‖))
      (fun y hy => (hd x y hy).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hB y hy x) hr₀ hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    have h1 : |(r - r₀)⁻¹ * (f r x - f r₀ x)| ≤ B * (1 + ‖x‖) := by
      rw [abs_mul, abs_inv]
      have hpos : 0 < |r - r₀| := abs_pos.2 hne'
      rw [inv_mul_le_iff₀ hpos]
      calc |f r x - f r₀ x| ≤ B * (1 + ‖x‖) * |r - r₀| := hmvt
        _ = _ := by ring
    have h2 := hB r₀ hr₀ x
    calc |(r - r₀)⁻¹ * (f r x - f r₀ x) - D r₀ x| ≤ |(r - r₀)⁻¹ * (f r x - f r₀ x)| + |D r₀ x| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  · intro x
    have := (hasDerivAt_iff_tendsto_slope.1 (hd x r₀ hr₀))
    have h2 := this.sub_const (D r₀ x)
    simp only [sub_self] at h2
    refine h2.congr fun r => ?_
    simp [slope_def_field, div_eq_inv_mul]

end HRS.MS.S79G
