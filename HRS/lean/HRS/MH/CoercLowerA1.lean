import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import HRS.Whole.Basic
import HRS.MH.CoercLowerDefs

/-!
# CoercLower, packets P07 (`gauss_overlap`) and P08 (`gaussK_basic`).

Statements are copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Integrability of `x ↦ exp(-t‖x‖²)` on `Euc d` for `t > 0`. -/
private theorem cla1_gaussK_integrable {t : ℝ} (ht : 0 < t) : Integrable (gaussK t : Euc d → ℝ) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (t : ℂ))
    (by simpa using ht) 0 0
  refine h.re.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [gaussK, Complex.exp_re, ← Complex.ofReal_pow]

/-- `∫ exp(-s‖x‖²) dx = (π/s)^{d/2}` on `Euc d` for `s > 0`. -/
private theorem cla1_gaussK_integral {s : ℝ} (hs : 0 < s) :
    ∫ x : Euc d, gaussK s x = (Real.pi / s) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euc d) hs
  rw [finrank_euclideanSpace_fin] at h
  simpa [gaussK] using h

/-- P08: basic facts on `gaussK t`. -/
theorem gaussK_basic {t : ℝ} (ht : 0 < t) :
    Continuous (gaussK t : Euc d → ℝ) ∧ (∀ x : Euc d, 0 < gaussK t x ∧ gaussK t x ≤ 1) ∧
      Integrable (gaussK t : Euc d → ℝ) ∧ ∫ x : Euc d, gaussK t x = (Real.pi / t) ^ ((d : ℝ) / 2) := by
  refine ⟨?_, ?_, cla1_gaussK_integrable ht, cla1_gaussK_integral ht⟩
  · unfold gaussK
    fun_prop
  · intro x
    unfold gaussK
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
    have : 0 ≤ t * ‖x‖ ^ 2 := by positivity
    linarith

/-- Pointwise identity: completing the square in the product of two Gaussians. -/
private theorem cla1_gaussK_mul_eq (t : ℝ) (x y z : Euc d) :
    gaussK (2 * t) (x - z) * gaussK (2 * t) (y - z) =
      gaussK (4 * t) (z - (1 / 2 : ℝ) • (x + y)) * gaussK t (x - y) := by
  unfold gaussK
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hpar := parallelogram_law_with_norm ℝ (x - z) (y - z)
  have h1 : ‖(x - z) + (y - z)‖ = 2 * ‖z - (1 / 2 : ℝ) • (x + y)‖ := by
    rw [show (x - z) + (y - z) = (-2 : ℝ) • (z - (1 / 2 : ℝ) • (x + y)) by module, norm_smul]
    norm_num
  have h2 : ‖(x - z) - (y - z)‖ = ‖x - y‖ := by congr 1; abel
  rw [h1, h2] at hpar
  linear_combination t * hpar

/-- P07: Gaussian overlap integral. -/
theorem gauss_overlap {t : ℝ} (ht : 0 < t) (x y : Euc d) :
    ∫ z, gaussK (2 * t) (x - z) * gaussK (2 * t) (y - z) =
      (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * gaussK t (x - y) := by
  simp_rw [cla1_gaussK_mul_eq t x y]
  rw [integral_mul_const, integral_sub_right_eq_self,
    cla1_gaussK_integral (by linarith : (0 : ℝ) < 4 * t)]
