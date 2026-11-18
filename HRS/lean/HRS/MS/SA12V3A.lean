import HRS.MS.SA12K22
import HRS.MS.SA12V3
import HRS.MS.SA12NearN6A
import HRS.MS.SA12BuildC18
import HRS.MS.SA12BuildC19
import HRS.MS.Ker1

/-!
# S.A.12 N1/N2 (SA12V3 worker), part A: convolution bounds against a mean-zero test function

`sa12v3_Test R B φ`: `φ` continuous, supported in `‖u‖ ≤ R`, `|φ| ≤ B`, `∫φ = 0`.  For a locally integrable kernel `f`
and a ball `closedBall a r'` containing `x - suppφ`, `|∫ f(x-u)φ(u)du| ≤ B ∫_{ball} Gm` whenever `|f - c| ≤ Gm` there
(the constant `c` is free because `∫φ = 0`).  `sa12vH γ ψ` has `partialDeriv idx (sa12vH γ ψ) = sa12vH γ (partialDeriv idx ψ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- A mean-zero test function with support radius `R` and sup bound `B`. -/
structure sa12v3_Test (R B : ℝ) (φ : Euc d → ℝ) : Prop where
  cont : Continuous φ
  supp : ∀ u : Euc d, R < ‖u‖ → φ u = 0
  bdd : ∀ u : Euc d, |φ u| ≤ B
  mean : ∫ u, φ u = 0

theorem sa12v3_Test.B_nonneg {R B : ℝ} {φ : Euc d → ℝ} (h : sa12v3_Test R B φ) : 0 ≤ B :=
  (abs_nonneg _).trans (h.bdd 0)

theorem sa12v3_Test.compact {R B : ℝ} {φ : Euc d → ℝ} (h : sa12v3_Test R B φ) : HasCompactSupport φ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R) (fun u hu => by
    apply h.supp
    simpa [Metric.mem_closedBall, dist_zero_right] using hu)

theorem sa12v3_Test.integrable {R B : ℝ} {φ : Euc d → ℝ} (h : sa12v3_Test R B φ) :
    Integrable φ volume := h.cont.integrable_of_hasCompactSupport h.compact

theorem sa12v3_lint {f : Euc d → ℝ} (hf : LocallyIntegrable f volume) {R B : ℝ} {φ : Euc d → ℝ}
    (h : sa12v3_Test R B φ) (x : Euc d) : Integrable (fun u => f (x - u) * φ u) volume := by
  have hc : HasCompactSupport (fun z : Euc d => φ (x - z)) :=
    HasCompactSupport.intro (isCompact_closedBall x R) (fun z hz => by
      apply h.supp
      rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hz
      rwa [← norm_neg, neg_sub] at hz)
  have h1 : Integrable (fun z : Euc d => f z * φ (x - z)) volume :=
    hf.integrable_smul_right_of_hasCompactSupport (h.cont.comp (continuous_const.sub continuous_id)) hc
  have h2 := (integrable_comp_sub_left (fun z : Euc d => f z * φ (x - z)) x).2 h1
  refine h2.congr (Eventually.of_forall fun u => ?_)
  simp

/-- Core estimate: cancel an arbitrary constant, bound by a nonnegative majorant on a ball. -/
theorem sa12v3_conv_le {f : Euc d → ℝ} (hf : LocallyIntegrable f volume) {R B : ℝ} {φ : Euc d → ℝ}
    (h : sa12v3_Test R B φ) (x a : Euc d) {r' : ℝ} (hr : ∀ u : Euc d, ‖u‖ ≤ R → x - u ∈ Metric.closedBall a r')
    (c : ℝ) (Gm : Euc d → ℝ) (hG0 : ∀ z, 0 ≤ Gm z) (hGi : IntegrableOn Gm (Metric.closedBall a r') volume)
    (hfG : ∀ᵐ z ∂(volume : Measure (Euc d)), z ∈ Metric.closedBall a r' → |f z - c| ≤ Gm z) :
    |∫ u, f (x - u) * φ u| ≤ B * ∫ z in Metric.closedBall a r', Gm z := by
  have hB := h.B_nonneg
  have hint := sa12v3_lint hf h x
  have hφi := h.integrable
  have e1 : ∫ u, f (x - u) * φ u = ∫ u, (f (x - u) - c) * φ u := by
    have : ∀ u, (f (x - u) - c) * φ u = f (x - u) * φ u - c * φ u := fun u => by ring
    simp_rw [this]
    rw [integral_sub hint (hφi.const_mul c), integral_const_mul, h.mean]; ring
  rw [e1]
  set G : Euc d → ℝ := (Metric.closedBall a r').indicator Gm with hGdef
  have hGi : Integrable G volume := (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 hGi
  have hG1 : Integrable (fun u => G (x - u)) volume := (integrable_comp_sub_left G x).2 hGi
  have hae : ∀ᵐ u ∂(volume : Measure (Euc d)), x - u ∈ Metric.closedBall a r' → |f (x - u) - c| ≤ Gm (x - u) :=
    (Measure.measurePreserving_sub_left (volume : Measure (Euc d)) x).quasiMeasurePreserving.ae hfG
  have hbd : ∀ᵐ u ∂(volume : Measure (Euc d)), ‖(f (x - u) - c) * φ u‖ ≤ B * G (x - u) := by
    filter_upwards [hae] with u hu1
    by_cases hu : ‖u‖ ≤ R
    · have hm := hr u hu
      rw [hGdef, indicator_of_mem hm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul (hu1 hm) (h.bdd u) (abs_nonneg _) (hG0 _)).trans (by rw [mul_comm])
    · rw [h.supp u (not_le.1 hu), mul_zero, norm_zero]
      exact mul_nonneg hB (by rw [hGdef]; exact indicator_nonneg (fun z _ => hG0 z) _)
  have h3 := norm_integral_le_of_norm_le (hG1.const_mul B) hbd
  rw [Real.norm_eq_abs] at h3
  refine h3.trans ?_
  rw [integral_const_mul, integral_sub_left_eq_self G volume x, hGdef,
    integral_indicator Metric.isClosed_closedBall.measurableSet]

end HRS.MH.AdjointRd.Phase2SA12V3
