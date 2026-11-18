import HRS.MS.S111X2Aux4

/-!
# S11.1 X2, packet E03 (part 1): differentiability of `L²(μ)`-valued paths from pointwise derivatives

`s111x2_lp_hasDerivAt`: if `r ↦ w r x` has derivative `w' r x` at every `r ∈ (a,b)` with `|w' r x| ≤ G x`, `G ∈ L²(μ)`,
then `r ↦ [w r]` is differentiable in `L²(μ)` with derivative `[w' r]` (dominated convergence + mean value theorem).
`s111x2_lp_continuousWithinAt`: continuity of the path on a closed interval from pointwise continuity and a uniform
`L²` bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole.Q34

variable {d : ℕ}

open Classical in
/-- The `L²(μ)` class of `f` (`0` if `f ∉ L²`). -/
def s111x2_toLp (μ : Measure (Euc d)) (f : Euc d → ℝ) : Lp ℝ 2 μ :=
  if h : MemLp f 2 μ then h.toLp f else 0

theorem s111x2_toLp_ae {μ : Measure (Euc d)} {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    (s111x2_toLp μ f : Euc d → ℝ) =ᵐ[μ] f := by
  unfold s111x2_toLp
  rw [dif_pos hf]
  exact MemLp.coeFn_toLp hf

theorem s111x2_lp_hasDerivAt {μ : Measure (Euc d)} [IsFiniteMeasure μ] {w w' : ℝ → Euc d → ℝ}
    {a b r A : ℝ} (hr : r ∈ Ioo a b) (hw : ∀ r' ∈ Ioo a b, MemLp (w r') 2 μ) (hw' : MemLp (w' r) 2 μ)
    (hder : ∀ x, ∀ r' ∈ Ioo a b, HasDerivAt (fun q => w q x) (w' r' x) r')
    (hbd : ∀ r' ∈ Ioo a b, ∀ x, |w' r' x| ≤ A * (1 + ‖x‖))
    (hG : MemLp (fun x : Euc d => A * (1 + ‖x‖)) 2 μ) :
    HasDerivAt (fun q => s111x2_toLp μ (w q)) (s111x2_toLp μ (w' r)) r := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  set l : Filter ℝ := 𝓝[≠] (0 : ℝ) with hl
  have hev : ∀ᶠ t in l, r + t ∈ Ioo a b := by
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), r + t ∈ Ioo a b := by
      have hc : ContinuousAt (fun t : ℝ => r + t) 0 := by fun_prop
      exact hc.eventually_mem (by simpa using Ioo_mem_nhds hr.1 hr.2)
    exact h2.filter_mono nhdsWithin_le_nhds
  set Fn : ℝ → Euc d → ℝ := fun t x => (t⁻¹ * (w (r + t) x - w r x) - w' r x) ^ 2 with hFn
  have hnorm : ∀ᶠ t in l, ‖t⁻¹ • (s111x2_toLp μ (w (r + t)) - s111x2_toLp μ (w r)) -
      s111x2_toLp μ (w' r)‖ = Real.sqrt (∫ x, Fn t x ∂μ) := by
    filter_upwards [hev] with t ht
    have e1 := s111x2_toLp_ae (hw _ ht)
    have e2 := s111x2_toLp_ae (hw r hr)
    have e3 := s111x2_toLp_ae hw'
    set U := t⁻¹ • (s111x2_toLp μ (w (r + t)) - s111x2_toLp μ (w r)) - s111x2_toLp μ (w' r) with hU
    have hae : (U : Euc d → ℝ) =ᵐ[μ] fun x => t⁻¹ * (w (r + t) x - w r x) - w' r x := by
      filter_upwards [Lp.coeFn_sub (t⁻¹ • (s111x2_toLp μ (w (r + t)) - s111x2_toLp μ (w r)))
        (s111x2_toLp μ (w' r)), Lp.coeFn_smul t⁻¹ (s111x2_toLp μ (w (r + t)) - s111x2_toLp μ (w r)),
        Lp.coeFn_sub (s111x2_toLp μ (w (r + t))) (s111x2_toLp μ (w r)), e1, e2, e3]
        with x h1 h2 h3 h4 h5 h6
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, h5, h6, smul_eq_mul]
    have := lp_norm_sq U
    rw [← Real.sqrt_sq (norm_nonneg U), this]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  refine (tendsto_congr' hnorm).2 ?_
  have hG2 : Integrable (fun x : Euc d => (2 * (A * (1 + ‖x‖))) ^ 2) μ := by
    have := hG.integrable_sq
    have := this.const_mul 4
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hint := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l) (F := Fn)
    (f := fun _ => (0 : ℝ)) (fun x => (2 * (A * (1 + ‖x‖))) ^ 2) ?_ ?_ hG2 ?_
  · have h0 : Tendsto (fun t => ∫ x, Fn t x ∂μ) l (𝓝 0) := by simpa using hint
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  · filter_upwards [hev] with t ht
    have h1 := (hw _ ht).aestronglyMeasurable
    have h2 := (hw r hr).aestronglyMeasurable
    have h3 := hw'.aestronglyMeasurable
    exact (((h1.sub h2).const_mul t⁻¹).sub h3).pow 2
  · filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
    have ht0 : t ≠ 0 := ht0
    refine Filter.Eventually.of_forall fun x => ?_
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun q => w q x)
      (f' := fun q => w' q x) (C := A * (1 + ‖x‖)) (s := Ioo a b)
      (fun q hq => (hder x q hq).hasDerivWithinAt) (fun q hq => by
        rw [Real.norm_eq_abs]; exact hbd q hq x) (convex_Ioo a b) hr ht
    simp only [Real.norm_eq_abs, add_sub_cancel_left] at hmvt
    have hG0 : 0 ≤ A * (1 + ‖x‖) := (abs_nonneg _).trans (hbd r hr x)
    have h1 : |t⁻¹ * (w (r + t) x - w r x)| ≤ A * (1 + ‖x‖) := by
      rw [abs_mul, abs_inv, inv_mul_eq_div, div_le_iff₀ (abs_pos.2 ht0)]
      rw [mul_comm] at hmvt ⊢
      exact hmvt
    have h2 := hbd r hr x
    have h3 : |t⁻¹ * (w (r + t) x - w r x) - w' r x| ≤ 2 * (A * (1 + ‖x‖)) := by
      refine (abs_sub _ _).trans ?_
      linarith
    rw [Real.norm_eq_abs, hFn]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (t⁻¹ * (w (r + t) x - w r x) - w' r x) ^ 2
        = |t⁻¹ * (w (r + t) x - w r x) - w' r x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * (A * (1 + ‖x‖))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := ((hder x r hr).tendsto_slope_zero)
    simp only [smul_eq_mul] at h1
    have h2 := (h1.sub_const (w' r x)).pow 2
    simpa [hFn] using h2

theorem s111x2_lp_continuousWithinAt {μ : Measure (Euc d)} [IsFiniteMeasure μ] {w : ℝ → Euc d → ℝ}
    {a b r : ℝ} (hr : r ∈ Icc a b) (hw : ∀ r' ∈ Icc a b, MemLp (w r') 2 μ)
    (hcont : ∀ x, ContinuousOn (fun q => w q x) (Icc a b)) {G : Euc d → ℝ}
    (hbd : ∀ r' ∈ Icc a b, ∀ x, |w r' x| ≤ G x) (hG : MemLp G 2 μ) :
    ContinuousWithinAt (fun q => s111x2_toLp μ (w q)) (Icc a b) r := by
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set l : Filter ℝ := 𝓝[Icc a b] r with hl
  have hev : ∀ᶠ q in l, q ∈ Icc a b := self_mem_nhdsWithin
  set Fn : ℝ → Euc d → ℝ := fun q x => (w q x - w r x) ^ 2 with hFn
  have hnorm : ∀ᶠ q in l, ‖s111x2_toLp μ (w q) - s111x2_toLp μ (w r)‖ = Real.sqrt (∫ x, Fn q x ∂μ) := by
    filter_upwards [hev] with q hq
    have e1 := s111x2_toLp_ae (hw _ hq)
    have e2 := s111x2_toLp_ae (hw r hr)
    set U := s111x2_toLp μ (w q) - s111x2_toLp μ (w r) with hU
    have hae : (U : Euc d → ℝ) =ᵐ[μ] fun x => w q x - w r x := by
      filter_upwards [Lp.coeFn_sub (s111x2_toLp μ (w q)) (s111x2_toLp μ (w r)), e1, e2]
        with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have := lp_norm_sq U
    rw [← Real.sqrt_sq (norm_nonneg U), this]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  refine (tendsto_congr' hnorm).2 ?_
  have hG2 : Integrable (fun x : Euc d => (2 * G x) ^ 2) μ := by
    have := hG.integrable_sq
    have := this.const_mul 4
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hint := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l) (F := Fn)
    (f := fun _ => (0 : ℝ)) (fun x => (2 * G x) ^ 2) ?_ ?_ hG2 ?_
  · have h0 : Tendsto (fun t => ∫ x, Fn t x ∂μ) l (𝓝 0) := by simpa using hint
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  · filter_upwards [hev] with q hq
    exact (((hw _ hq).aestronglyMeasurable.sub (hw r hr).aestronglyMeasurable)).pow 2
  · filter_upwards [hev] with q hq
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 := hbd q hq x
    have h2 := hbd r hr x
    have h3 : |w q x - w r x| ≤ 2 * G x := by
      refine (abs_sub _ _).trans ?_
      linarith
    rw [Real.norm_eq_abs, hFn]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (w q x - w r x) ^ 2 = |w q x - w r x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * G x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (hcont x r hr).tendsto
    have h2 := (h1.sub_const (w r x)).pow 2
    simpa [hFn] using h2

end HRS.MS.S111X2
