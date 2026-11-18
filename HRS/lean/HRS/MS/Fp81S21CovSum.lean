import HRS.MS.Fp81S21CovMeas3

/-!
# S2.1(iii), packet 16b: summing blockwise covariance controls

This file starts with a generic measure-theoretic summation lemma. Its
partition premise is explicit so later physical applications must prove the
block tiling (including the null shared-endpoint convention) rather than hide
it in a change of interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

/-- Sum blockwise norm bounds into one source integral. The block integrands
are AEMeasurable, and `hpartition` is the precise integral/tsum handoff that a
physical tiling proof must supply. Finiteness of both the summed bound and the
source integral is included in the conclusion. -/
theorem fp81s21_tsum_norm_le_integral_of_blockwise
    {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (f : ℝ → ℝ≥0∞) (B : ℕ → Set ℝ) (S : Set ℝ)
    (K : ℝ≥0∞)
    (hK : K < ∞)
    (hf : AEMeasurable f volume)
    (hB : ∀ k, MeasurableSet (B k))
    (hblock : ∀ k, ‖x k‖ₑ ≤ K * (∫⁻ t in B k, f t))
    (hpartition : ∫⁻ t, ∑' k, (B k).indicator f t ∂volume ≤ ∫⁻ t in S, f t)
    (hsource : ∫⁻ t in S, f t < ∞) :
    (∑' k, ‖x k‖ₑ ≤ K * (∫⁻ t in S, f t)) ∧
      (∑' k, ‖x k‖ₑ < ∞) := by
  have hmeas : ∀ k, AEMeasurable (fun t => (B k).indicator f t) volume := by
    intro k
    exact hf.indicator (hB k)
  have hswap :
      (∑' k, ∫⁻ t in B k, f t) = ∫⁻ t, ∑' k, (B k).indicator f t ∂volume := by
    calc
      (∑' k, ∫⁻ t in B k, f t) =
          ∑' k, ∫⁻ t, (B k).indicator f t ∂volume := by
            apply tsum_congr
            intro k
            exact (lintegral_indicator (hB k) f).symm
      _ = ∫⁻ t, ∑' k, (B k).indicator f t ∂volume := by
            rw [lintegral_tsum hmeas]
  have hsum : (∑' k, ∫⁻ t in B k, f t) ≤ ∫⁻ t in S, f t := by
    rw [hswap]
    exact hpartition
  have hnorm : ∑' k, ‖x k‖ₑ ≤ K * (∫⁻ t in S, f t) := by
    calc
      (∑' k, ‖x k‖ₑ) ≤ ∑' k, K * (∫⁻ t in B k, f t) :=
        ENNReal.tsum_le_tsum hblock
      _ = K * (∑' k, ∫⁻ t in B k, f t) := ENNReal.tsum_mul_left
      _ ≤ K * (∫⁻ t in S, f t) := by
            simpa [mul_comm] using (mul_le_mul_left hsum K)
  refine ⟨hnorm, ?_⟩
  exact lt_of_le_of_lt hnorm (ENNReal.mul_lt_top hK hsource)

#print axioms fp81s21_tsum_norm_le_integral_of_blockwise

end HRS.Fp81.S21

end
