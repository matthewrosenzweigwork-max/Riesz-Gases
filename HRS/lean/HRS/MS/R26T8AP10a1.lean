import HRS.MS.R26T8AP11a
import HRS.MS.R26T8AP00b
import HRS.MS.S82P2Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# S8.2 T8A P10a (part 1): Gaussian-times-pole majorants and integrability
`R26P10GP y τ φ`: `|φ u| ≤ C e^{-c|u|²}(1 + |u-y|^{-τ})` for `u ≠ y`.
`r26t8a_p10a_gp_dom`: such a majorant is integrable for `0 < τ < d`.
`r26t8a_p10a_poly_gauss`: polynomial weight times Gaussian is dominated by a Gaussian.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_gauss_int {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Euc d => Real.exp (-b * ‖v‖ ^ 2)) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d)
    (b := (b:ℂ)) (by simpa using hb) 0 0
  have h2 := this.norm
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  have : (-(b:ℂ) * (‖v‖:ℂ) ^ 2).re = -b * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]

/-- polynomial times Gaussian is dominated by a Gaussian of half the rate. -/
theorem r26t8a_p10a_poly_gauss (N : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ C * Real.exp (-(c / 2) * r ^ 2) := by
  set n := ⌈N⌉₊ with hn
  refine ⟨(n.factorial : ℝ) * Real.exp 1 * Real.exp (1 / (2 * c)), by positivity, fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ (1 + r) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil N)
  have h2 : (1 + r) ^ (n : ℝ) = (1 + r) ^ n := Real.rpow_natCast _ _
  have h3 : (1 + r) ^ n ≤ n.factorial * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by linarith) n
    have hf : (0 : ℝ) < n.factorial := by positivity
    rw [div_le_iff₀ hf] at this
    linarith
  have h4 : Real.exp (1 + r) * Real.exp (-c * r ^ 2) ≤
      Real.exp 1 * Real.exp (1 / (2 * c)) * Real.exp (-(c / 2) * r ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : r - c / 2 * r ^ 2 ≤ 1 / (2 * c) := by
      have hc2 : 0 < 2 * c := by linarith
      rw [le_div_iff₀ hc2]
      nlinarith [sq_nonneg (c * r - 1)]
    nlinarith
  calc (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ (n.factorial * Real.exp (1 + r)) * Real.exp (-c * r ^ 2) := by
        rw [h2] at h1
        exact mul_le_mul_of_nonneg_right (h1.trans h3) (Real.exp_pos _).le
    _ = n.factorial * (Real.exp (1 + r) * Real.exp (-c * r ^ 2)) := by ring
    _ ≤ n.factorial * (Real.exp 1 * Real.exp (1 / (2 * c)) * Real.exp (-(c / 2) * r ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-- Gaussian times a pole of order `τ` at `y`. -/
def R26P10GP (y : Euc d) (τ : ℝ) (φ : Euc d → ℝ) : Prop :=
  ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ u, u ≠ y →
    |φ u| ≤ C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))

theorem r26t8a_p10a_pole_on (hd : 2 ≤ d) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < d) (y : Euc d) {R : ℝ}
    (hR : 0 < R) : IntegrableOn (fun u : Euc d => ‖u - y‖ ^ (-τ)) (ball y R) := by
  have hm := (r26t8a_p11a_mass d hd ((d : ℝ) - τ) (by linarith) (by linarith) R hR).1
  have e : (d : ℝ) - τ - d = -τ := by ring
  rw [e] at hm
  have h1 : Integrable (Set.indicator (ball (0 : Euc d) R) (fun z : Euc d => ‖z‖ ^ (-τ))) := by
    rwa [integrable_indicator_iff measurableSet_ball]
  have h2 := h1.comp_sub_right y
  refine (integrable_indicator_iff measurableSet_ball).1
    (h2.congr (Filter.Eventually.of_forall fun u => ?_))
  by_cases hu : u ∈ ball y R
  · have : u - y ∈ ball (0 : Euc d) R := by simpa [mem_ball_iff_norm, dist_eq_norm] using hu
    simp [Set.indicator_of_mem hu, Set.indicator_of_mem this]
  · have : u - y ∉ ball (0 : Euc d) R := by simpa [mem_ball_iff_norm, dist_eq_norm] using hu
    simp [Set.indicator_of_notMem hu, Set.indicator_of_notMem this]

theorem r26t8a_p10a_gp_dom (hd : 2 ≤ d) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < d) (y : Euc d) {c : ℝ}
    (hc : 0 < c) :
    Integrable (fun u : Euc d => Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))) := by
  have hg := r26t8a_p10a_gauss_int (d := d) hc
  have hmP : Measurable (fun u : Euc d => ‖u - y‖ ^ (-τ)) :=
    (measurable_id.sub_const y).norm.pow_const _
  have hmeas : AEStronglyMeasurable
      (fun u : Euc d => Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))) volume :=
    (Continuous.aestronglyMeasurable (by fun_prop)).mul (measurable_const.add hmP).aestronglyMeasurable
  have hb : IntegrableOn
      (fun u : Euc d => Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))) (ball y 1) := by
    have hp := r26t8a_p10a_pole_on hd hτ0 hτ y one_pos
    have hone : IntegrableOn (fun _ : Euc d => (1 : ℝ)) (ball y 1) :=
      integrableOn_const (by exact measure_ball_lt_top.ne)
    refine Integrable.mono' (hone.add hp) hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h0 : 0 ≤ ‖u - y‖ ^ (-τ) := Real.rpow_nonneg (norm_nonneg _) _
    have he : Real.exp (-c * ‖u‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖u‖])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [Real.exp_pos (-c * ‖u‖ ^ 2)]
  have hc' : IntegrableOn
      (fun u : Euc d => Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))) (ball y 1)ᶜ := by
    refine Integrable.mono' (hg.const_mul 2).integrableOn hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : 1 ≤ ‖u - y‖ := by simpa [mem_ball_iff_norm, dist_eq_norm, not_lt] using hu
    have h0 : ‖u - y‖ ^ (-τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu' (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Real.exp_pos (-c * ‖u‖ ^ 2)]
  have := hb.union hc'
  rwa [Set.union_compl_self, integrableOn_univ] at this

end HRS.MS.R26T8A
