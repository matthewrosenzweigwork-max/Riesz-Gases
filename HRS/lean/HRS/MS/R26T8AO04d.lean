import HRS.MS.R26T8AO04c

/-!
# S8.2 T8A O04 (part d): the noise energy at a fixed time
At time `r ∈ [0,b]` the path has the Gibbs law, so by the `NormalFormFamily` energy bound applied to the age
test function `ageTest j (b - r)` (a `TestBound` with constant `Cf * weight * exp(-c (b-r))`) the energy of
`noiseAge` is at most `(2/β) (C Cf weight)² / N * exp(-2c(b-r))`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

theorem r26t8a_o04_enorm_sq_sqrt {s : ℝ} (hs : 0 ≤ s) (y : ℝ) :
    ‖Real.sqrt s * y‖ₑ ^ 2 = ENNReal.ofReal s * ‖y‖ₑ ^ 2 := by
  rw [enorm_mul, Real.enorm_of_nonneg (Real.sqrt_nonneg s), mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg s),
    Real.sq_sqrt hs]

theorem r26t8a_o04_sum_enorm_sq (v : Euc d) : ∑ k, ‖v k‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  have h1 : ∀ k, ‖v k‖ₑ ^ 2 = ENNReal.ofReal (‖v k‖ ^ 2) := fun k => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [h1, h2]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), EuclideanSpace.norm_sq_eq]

end HRS.MS.R26T8A

end
