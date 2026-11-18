import Mathlib

/-!
# S.A.16 (SA16Y3) L2a: `L^2` Cauchy-Schwarz in `eLpNorm` form (packet P7, Hilbert corner)

`sa16y3_N2 f = (‖f‖_{L^2}).toReal`; `sa16y3_N2_sq`: `∫ f² = N2(f)²`; `sa16y3_cs`: `|∫ f g| ≤ N2 f N2 g`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section L2a
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- the `L^2` norm as a real number -/
def sa16y3_N2 (f : X → ℝ) (μ : Measure X) : ℝ := (eLpNorm f (ENNReal.ofReal 2) μ).toReal

lemma sa16y3_N2_eq {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal 2) μ) :
    sa16y3_N2 f μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
  unfold sa16y3_N2
  have h := hf.eLpNorm_eq_integral_rpow_norm (by simp) (by simp)
  rw [h, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)]
  simp

lemma sa16y3_N2_nonneg (f : X → ℝ) : 0 ≤ sa16y3_N2 f μ := ENNReal.toReal_nonneg

lemma sa16y3_N2_sq {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal 2) μ) :
    ∫ x, f x ^ 2 ∂μ = sa16y3_N2 f μ ^ 2 := by
  rw [sa16y3_N2_eq hf, ← Real.rpow_natCast, ← Real.rpow_mul
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  norm_num

lemma sa16y3_cs {f g : X → ℝ} (hf : MemLp f (ENNReal.ofReal 2) μ) (hg : MemLp g (ENNReal.ofReal 2) μ) :
    |∫ x, f x * g x ∂μ| ≤ sa16y3_N2 f μ * sa16y3_N2 g μ := by
  refine (abs_integral_le_integral_abs).trans ?_
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖) (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) hf.norm hg.norm
  rw [sa16y3_N2_eq hf, sa16y3_N2_eq hg]
  simp only [Real.norm_eq_abs] at h ⊢
  simpa [one_div] using h

end L2a

end HRS.Whole.AppendixA.Phase2SA16R
