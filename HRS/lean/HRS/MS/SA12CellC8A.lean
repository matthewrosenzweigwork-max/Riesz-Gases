import HRS.MH.AdjointRdDefs
import HRS.MS.SA12CellR35

/-!
# S.A.12 C8 (part A): differentiation under the integral sign on a compact time interval
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- Differentiation of a parametric integral within `[0,t]`: pointwise time derivatives, a uniform
support radius and uniform bounds on the function and on its time derivative. -/
theorem sa12y_param_deriv {t : ℝ} {f f' : ℝ → Euc d → ℝ} {R K : ℝ}
    (hmeas : ∀ σ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (f σ) volume)
    (hsupp : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, R < ‖x‖ → f σ x = 0)
    (hbd : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |f σ x| ≤ K)
    (hder : ∀ x, ∀ σ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun τ' => f τ' x) (f' σ x) (Icc (0 : ℝ) t) σ)
    (hdbd : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, ‖x‖ ≤ R → |f' σ x| ≤ K)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => ∫ x, f τ' x) (∫ x, f' τ x) (Icc (0 : ℝ) t) τ := by
  set ball : Set (Euc d) := Metric.closedBall 0 R with hball
  have hind : Integrable (ball.indicator (fun _ => K)) volume :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hK0 : 0 ≤ K := by
    have := hbd τ hτ 0
    exact (abs_nonneg _).trans this
  have hfint : ∀ σ ∈ Icc (0 : ℝ) t, Integrable (f σ) volume := by
    intro σ hσ
    refine Integrable.mono' hind (hmeas σ hσ) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : ‖x‖ ≤ R
    · have hxb : x ∈ ball := by simpa [hball] using hx
      rw [Set.indicator_of_mem hxb]; exact hbd σ hσ x
    · push Not at hx
      rw [hsupp σ hσ x hx, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => hK0) x
  rw [hasDerivWithinAt_iff_tendsto_slope]
  set l : Filter ℝ := 𝓝[Icc (0 : ℝ) t \ {τ}] τ with hl
  have hmem : Icc (0 : ℝ) t \ {τ} ∈ l := self_mem_nhdsWithin
  have hslope : ∀ τ' ∈ Icc (0 : ℝ) t \ {τ}, slope (fun σ => ∫ x, f σ x) τ τ' =
      ∫ x, (τ' - τ)⁻¹ * (f τ' x - f τ x) := by
    intro τ' hτ'
    rw [slope_def_field, ← integral_sub (hfint τ' hτ'.1) (hfint τ hτ), div_eq_inv_mul,
      ← integral_const_mul]
  have hlim : Tendsto (fun τ' => ∫ x, (τ' - τ)⁻¹ * (f τ' x - f τ x)) l (𝓝 (∫ x, f' τ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (ball.indicator (fun _ => K)) ?_ ?_ hind ?_
    · filter_upwards [hmem] with τ' hτ'
      exact ((hmeas τ' hτ'.1).sub (hmeas τ hτ)).const_mul _
    · filter_upwards [hmem] with τ' hτ'
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      by_cases hx : ‖x‖ ≤ R
      · have hxb : x ∈ ball := by simpa [hball] using hx
        rw [Set.indicator_of_mem hxb]
        have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ => f σ x)
          (f' := fun σ => f' σ x) (C := K) (s := Icc (0 : ℝ) t) (x := τ) (y := τ')
          (fun σ hσ => hder x σ hσ) (fun σ hσ => by rw [Real.norm_eq_abs]; exact hdbd σ hσ x hx)
          (convex_Icc 0 t) hτ hτ'.1
        rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
        have hne : τ' - τ ≠ 0 := sub_ne_zero.2 hτ'.2
        rw [abs_mul, abs_inv]
        have hpos : 0 < |τ' - τ| := abs_pos.2 hne
        rw [inv_mul_le_iff₀ hpos]
        simpa [mul_comm] using hmvt
      · push Not at hx
        rw [hsupp τ' hτ'.1 x hx, hsupp τ hτ x hx, sub_zero, mul_zero, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => hK0) x
    · refine Eventually.of_forall fun x => ?_
      have := (hasDerivWithinAt_iff_tendsto_slope.1 (hder x τ hτ))
      refine this.congr fun τ' => ?_
      simp [slope_def_field, div_eq_inv_mul]
  refine hlim.congr' ?_
  filter_upwards [hmem] with τ' hτ'
  exact (hslope τ' hτ').symm

end HRS.MH.AdjointRd.Phase2SA12Construction
