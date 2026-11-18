import HRS.External.WeakSpec
import HRS.MS.S82RM2

/-!
# S8.2 R02 (S82R), M15: one-change and pin-addition estimates for the one-site densities
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

/-- `d_c(z,u) = 1 - exp(-c q(z,u))`. -/
def s82r_d {μ : Measure E} (V : WeakPotential μ) (c : ℝ) (z u : E) : ℝ :=
  1 - Real.exp (-(c * V.q z u))

lemma s82r_d_nonneg {μ : Measure E} (V : WeakPotential μ) {c : ℝ} (hc : 0 ≤ c) (z u : E) :
    0 ≤ s82r_d V c z u := by
  unfold s82r_d
  have : Real.exp (-(c * V.q z u)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [V.q_nonneg z u])
  linarith

lemma s82r_d_le {μ : Measure E} (V : WeakPotential μ) {c : ℝ} (hc : 0 ≤ c) (z u : E) :
    s82r_d V c z u ≤ c * V.q z u := by
  unfold s82r_d
  have := Real.add_one_le_exp (-(c * V.q z u))
  linarith

lemma s82r_d_lt_one {μ : Measure E} (V : WeakPotential μ) (c : ℝ) (z u : E) :
    s82r_d V c z u ≤ 1 := by
  unfold s82r_d
  have := Real.exp_pos (-(c * V.q z u))
  linarith

lemma s82r_d_meas {μ : Measure E} (V : WeakPotential μ) (c : ℝ) (u : E) :
    Measurable (fun z => s82r_d V c z u) := by
  unfold s82r_d
  exact measurable_const.sub (Real.measurable_exp.comp
    ((V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul c).neg)

lemma s82r_d_int {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {c : ℝ} (hc : 0 ≤ c)
    (u : E) : ∫ z, s82r_d V c z u ∂μ ≤ c * V.γ := by
  have hi : Integrable (fun z => c * V.q z u) μ := (integrable_q_left V u).const_mul c
  have hdi : Integrable (fun z => s82r_d V c z u) μ :=
    Integrable.of_bound (s82r_d_meas V c u).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (s82r_d_nonneg V hc z u)]; exact s82r_d_lt_one V c z u)
  calc ∫ z, s82r_d V c z u ∂μ ≤ ∫ z, c * V.q z u ∂μ :=
        integral_mono hdi hi fun z => s82r_d_le V hc z u
    _ = c * ∫ z, V.q z u ∂μ := integral_const_mul _ _
    _ ≤ c * V.γ := mul_le_mul_of_nonneg_left (integral_q_left_le V u) hc

lemma s82r_exp_diff_le {μ : Measure E} (V : WeakPotential μ) {c : ℝ} (hc : 0 ≤ c) (z u u' : E) :
    |Real.exp (-(c * V.q z u)) - Real.exp (-(c * V.q z u'))| ≤ s82r_d V c z u + s82r_d V c z u' := by
  unfold s82r_d
  have h1 := Real.exp_pos (-(c * V.q z u))
  have h2 := Real.exp_pos (-(c * V.q z u'))
  have h3 : Real.exp (-(c * V.q z u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [V.q_nonneg z u])
  have h4 : Real.exp (-(c * V.q z u')) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [V.q_nonneg z u'])
  rw [abs_le]; constructor <;> linarith

end HRS.MS.S82R

end
