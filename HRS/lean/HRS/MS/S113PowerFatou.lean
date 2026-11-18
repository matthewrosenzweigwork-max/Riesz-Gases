import Mathlib

/-!
# S11.3.F1 (breakdown packet F1): Fatou transfer of a uniform power bound along an a.e. convergent sequence
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S113BD

variable {α : Type*} [MeasurableSpace α]

theorem s113_power_fatou (Q : Measure α)
    (r : ℕ → α → ℝ) (h : α → ℝ)
    (hr : ∀ n, Measurable (r n)) (hh : Measurable h)
    (hr0 : ∀ n x, 0 ≤ r n x) (hh0 : ∀ x, 0 ≤ h x)
    (p K : ℝ) (hp : 1 < p)
    (hconv : ∀ᵐ x ∂Q, Tendsto (fun n => r n x) atTop (𝓝 (h x)))
    (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (r n x ^ p) ∂Q ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (h x ^ p) ∂Q ≤ ENNReal.ofReal K := by
  have hp0 : 0 < p := by linarith
  have hlim : ∀ᵐ x ∂Q, Tendsto (fun n => ENNReal.ofReal (r n x ^ p)) atTop (𝓝 (ENNReal.ofReal (h x ^ p))) := by
    filter_upwards [hconv] with x hx
    have h1 : Tendsto (fun n => r n x ^ p) atTop (𝓝 (h x ^ p)) :=
      (Real.continuousAt_rpow_const (h x) p (Or.inr hp0.le)).tendsto.comp hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  calc ∫⁻ x, ENNReal.ofReal (h x ^ p) ∂Q
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (r n x ^ p)) atTop ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with x hx
        exact hx.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (r n x ^ p) ∂Q) atTop :=
        lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp ((hr n).pow_const p))
    _ ≤ ENNReal.ofReal K := by
        refine liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound).frequently
          |>.trans ?_
        exact le_rfl

end HRS.MS.S113BD
