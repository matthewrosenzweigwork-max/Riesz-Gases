import HRS.MS.R26T6CI18Cube
import HRS.MS.S111X2Aux13

/-! R26-T6C.I18: L³-valued differentiability from uniform pointwise derivative bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6C
open HRS HRS.Whole
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

def r26t6c_toLp3 {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (f : X → ℝ) : Lp ℝ 3 mu :=
  if h : MemLp f 3 mu then h.toLp f else 0

theorem r26t6c_toLp3_ae {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {f : X → ℝ} (hf : MemLp f 3 mu) :
    (r26t6c_toLp3 mu f : X → ℝ) =ᵐ[mu] f := by
  unfold r26t6c_toLp3
  rw [dif_pos hf]
  exact MemLp.coeFn_toLp hf

theorem r26t6c_L3_hasDerivAt {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w w' : ℝ → X → ℝ) (G : X → ℝ)
    (a b t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hw : ∀ q ∈ Set.Ioo a b, MemLp (w q) 3 mu)
    (hw' : MemLp (w' t) 3 mu) (hG : MemLp G 3 mu)
    (hder : ∀ x q, q ∈ Set.Ioo a b → HasDerivAt (fun r => w r x) (w' q x) q)
    (hbd : ∀ q ∈ Set.Ioo a b, ∀ x, |w' q x| ≤ G x) :
    HasDerivAt (fun q => r26t6c_toLp3 mu (w q))
      (r26t6c_toLp3 mu (w' t)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  set l : Filter ℝ := 𝓝[≠] (0 : ℝ) with hl
  have hev : ∀ᶠ s in l, t + s ∈ Set.Ioo a b := by
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ Set.Ioo a b := by
      have hc : ContinuousAt (fun s : ℝ => t + s) 0 := by fun_prop
      exact hc.eventually_mem (by simpa using Ioo_mem_nhds ht.1 ht.2)
    exact h2.filter_mono nhdsWithin_le_nhds
  set Fn : ℝ → X → ℝ := fun s x =>
    |s⁻¹ * (w (t + s) x - w t x) - w' t x| ^ 3 with hFn
  have hnorm : ∀ᶠ s in l,
      ‖s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) - r26t6c_toLp3 mu (w t)) -
        r26t6c_toLp3 mu (w' t)‖ ^ 3 = ∫ x, Fn s x ∂mu := by
    filter_upwards [hev] with s hs
    have e1 := r26t6c_toLp3_ae (hw _ hs)
    have e2 := r26t6c_toLp3_ae (hw t ht)
    have e3 := r26t6c_toLp3_ae hw'
    set U : Lp ℝ 3 mu :=
      s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) - r26t6c_toLp3 mu (w t)) -
        r26t6c_toLp3 mu (w' t) with hU
    have hae : (U : X → ℝ) =ᵐ[mu] fun x =>
        s⁻¹ * (w (t + s) x - w t x) - w' t x := by
      filter_upwards [
        Lp.coeFn_sub (s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) -
          r26t6c_toLp3 mu (w t))) (r26t6c_toLp3 mu (w' t)),
        Lp.coeFn_smul s⁻¹ (r26t6c_toLp3 mu (w (t + s)) -
          r26t6c_toLp3 mu (w t)),
        Lp.coeFn_sub (r26t6c_toLp3 mu (w (t + s))) (r26t6c_toLp3 mu (w t)),
        e1, e2, e3] with x h1 h2 h3 h4 h5 h6
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply,
        h4, h5, h6, smul_eq_mul]
    change ‖U‖ ^ 3 = _
    rw [r26t6c_Lp_norm_cube mu U]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have hGnonneg : ∀ x, 0 ≤ G x := fun x =>
    (abs_nonneg _).trans (hbd t ht x)
  have hG3 : Integrable (fun x => (2 * |G x|) ^ 3) mu := by
    have hi := hG.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    have hi8 := hi.const_mul 8
    refine hi8.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    ring
  have hint := tendsto_integral_filter_of_dominated_convergence
    (μ := mu) (l := l) (F := Fn) (f := fun _ => (0 : ℝ))
    (fun x => (2 * |G x|) ^ 3) ?_ ?_ hG3 ?_
  · have h0 : Tendsto (fun s => ∫ x, Fn s x ∂mu) l (𝓝 0) := by
      simpa using hint
    have hcubed : Tendsto (fun s =>
        ‖s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) - r26t6c_toLp3 mu (w t)) -
          r26t6c_toLp3 mu (w' t)‖ ^ 3) l (𝓝 0) :=
      (tendsto_congr' hnorm).2 h0
    have hroot := (Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 1 / 3)).tendsto (0 : ℝ) |>.comp hcubed
    have hroot0 : Tendsto (fun s =>
        (‖s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) - r26t6c_toLp3 mu (w t)) -
          r26t6c_toLp3 mu (w' t)‖ ^ 3) ^ (1 / 3 : ℝ)) l (𝓝 0) := by
      simpa [Function.comp_def] using hroot
    convert hroot0 using 1
    ext s
    have hn : 0 ≤ ‖s⁻¹ • (r26t6c_toLp3 mu (w (t + s)) -
        r26t6c_toLp3 mu (w t)) - r26t6c_toLp3 mu (w' t)‖ :=
      norm_nonneg _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    norm_num
  · filter_upwards [hev] with s hs
    have hm : AEStronglyMeasurable
        (fun x => s⁻¹ * (w (t+s) x - w t x) - w' t x) mu :=
      (((hw _ hs).aestronglyMeasurable.sub
        (hw t ht).aestronglyMeasurable).const_mul s⁻¹).sub
        hw'.aestronglyMeasurable
    have hpow : ((fun x : X => ‖s⁻¹ * (w (t+s) x - w t x) - w' t x‖) ^ (3:ℕ)) =
        (fun x : X => ‖s⁻¹ * (w (t+s) x - w t x) - w' t x‖ ^ 3) := by
      funext x
      rfl
    have hmp := hm.norm.pow 3
    rw [hpow] at hmp
    simpa [hFn, Real.norm_eq_abs] using hmp
  · filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
    have hs0 : s ≠ 0 := hs0
    refine Filter.Eventually.of_forall fun x => ?_
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun q => w q x) (f' := fun q => w' q x) (C := G x)
      (s := Set.Ioo a b)
      (fun q hq => (hder x q hq).hasDerivWithinAt)
      (fun q hq => by rw [Real.norm_eq_abs]; exact hbd q hq x)
      (convex_Ioo a b) ht hs
    simp only [Real.norm_eq_abs, add_sub_cancel_left] at hmvt
    have h1 : |s⁻¹ * (w (t + s) x - w t x)| ≤ G x := by
      rw [abs_mul, abs_inv, inv_mul_eq_div, div_le_iff₀ (abs_pos.2 hs0)]
      rw [mul_comm] at hmvt ⊢
      exact hmvt
    have h2 := hbd t ht x
    have h3 : |s⁻¹ * (w (t + s) x - w t x) - w' t x| ≤
        2 * |G x| := by
      calc
        _ ≤ |s⁻¹ * (w (t + s) x - w t x)| + |w' t x| :=
          abs_sub _ _
        _ ≤ G x + G x := add_le_add h1 h2
        _ = 2 * |G x| := by rw [abs_of_nonneg (hGnonneg x)]; ring
    rw [Real.norm_eq_abs, hFn]
    simp only
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 3
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (hder x t ht).tendsto_slope_zero
    simp only [smul_eq_mul] at h1
    have h2 := (h1.sub_const (w' t x)).abs.pow 3
    simpa [hFn] using h2

end HRS.MS.R26T6C
