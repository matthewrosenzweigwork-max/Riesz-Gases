import Mathlib
import HRS.MC.S7W4
import HRS.MC.S7E0b

/-!
# Packet `s7_E4_normalized_clt`, file 2: the abstract approximation argument

If `Q_n` are `L^2` random variables with `E Q_n^2 -> infinity` and each `Q_n` is `L^2`-approximated, to any
accuracy, by variables with the law of `(1/2) sum_k a_k (g_k^2 - 1)` with eigenvalues bounded by a
constant `Lam`, then `Q_n / sigma_n` converges in distribution to `N(0,1)` (`W4` and Slutsky).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E4A2

open HRS.MC.Sec7.W4

section Moment

variable {L : ℕ}

theorem quad_second (a : Fin L → ℝ) :
    ∫ y : Fin L → ℝ, ((1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) ^ 2
        ∂(Measure.pi fun _ : Fin L => gaussianReal 0 1) = (1 / 2 : ℝ) * ∑ k, a k ^ 2 := by
  set μ : Measure (Fin L → ℝ) := Measure.pi fun _ : Fin L => gaussianReal 0 1 with hμ
  set X : Fin L → ℝ → ℝ := fun k t => a k * (t ^ 2 - 1) with hXdef
  have h1 : MemLp (fun t : ℝ => t ^ 2 - 1) 2 (gaussianReal 0 1) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have : ∀ y : ℝ, (y ^ 2 - 1) ^ 2 = y ^ 4 - 2 * y ^ 2 + 1 := fun y => by ring
    simp_rw [this]
    exact ((s7w4_int_pow 4).sub ((s7w4_int_pow 2).const_mul 2)).add (integrable_const _)
  have hX : ∀ k, MemLp (X k) 2 (gaussianReal 0 1) := fun k => h1.const_mul _
  have hv := variance_sum_pi (μ := fun _ : Fin L => gaussianReal 0 1) (X := X) hX
  have hXm : ∀ k, Integrable (fun y : Fin L → ℝ => X k (y k)) μ := fun k =>
    ((hX k).comp_measurePreserving (measurePreserving_eval _ k)).integrable one_le_two
  have hXint : ∀ k, ∫ y : Fin L → ℝ, X k (y k) ∂μ = 0 := by
    intro k
    have hmp := (measurePreserving_eval (fun _ : Fin L => gaussianReal 0 1) k).map_eq
    have hae : AEStronglyMeasurable (X k) (Measure.map (fun f : Fin L → ℝ => f k) μ) := by
      rw [hmp]; exact (hX k).aestronglyMeasurable
    have := integral_map (μ := μ) (measurable_pi_apply k).aemeasurable (f := X k) hae
    rw [hmp] at this
    rw [← this]
    simp only [hXdef]
    rw [integral_const_mul, s7w4_intY, mul_zero]
  have hmean : ∫ y : Fin L → ℝ, ∑ k, X k (y k) ∂μ = 0 := by
    rw [integral_finsetSum _ fun k _ => hXm k]
    exact Finset.sum_eq_zero fun k _ => hXint k
  have hvar : ∀ k, Var[X k; gaussianReal 0 1] = 2 * a k ^ 2 := by
    intro k
    have h0 : (gaussianReal 0 1)[X k] = 0 := by
      simp only [hXdef]; rw [integral_const_mul, s7w4_intY, mul_zero]
    rw [variance_of_integral_eq_zero (hX k).aestronglyMeasurable.aemeasurable h0]
    simp only [hXdef, mul_pow]
    rw [integral_const_mul, s7w4_intY2]; ring
  have hsum : Var[∑ k, fun y : Fin L → ℝ => X k (y k); μ] = ∫ y, (∑ k, X k (y k)) ^ 2 ∂μ := by
    have hmeas : AEMeasurable (∑ k, fun y : Fin L → ℝ => X k (y k)) μ := by
      have : Measurable (∑ k, fun y : Fin L → ℝ => X k (y k)) := by
        simp only [hXdef]; fun_prop
      exact this.aemeasurable
    rw [variance_of_integral_eq_zero hmeas (by
      simpa [Finset.sum_apply] using hmean)]
    simp [Finset.sum_apply]
  have key : ∫ y, (∑ k, X k (y k)) ^ 2 ∂μ = ∑ k, 2 * a k ^ 2 := by
    rw [← hsum, hv]
    exact Finset.sum_congr rfl fun k _ => hvar k
  have e : ∀ y : Fin L → ℝ, ((1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) ^ 2 =
      (1 / 4 : ℝ) * (∑ k, X k (y k)) ^ 2 := fun y => by simp only [hXdef]; ring
  simp_rw [e]
  rw [integral_const_mul, key, ← Finset.mul_sum]
  ring

end Moment

end HRS.MC.Sec7.E4A2

end
