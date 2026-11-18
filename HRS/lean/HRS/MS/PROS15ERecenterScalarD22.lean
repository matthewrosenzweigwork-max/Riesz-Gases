import HRS.MS.PROS15EChaosHS

/-!
# S15e: summability of the Gaussian covariance recentering correction

The Hilbert--Schmidt eigenvalues need only be square-summable, not
trace-class. Under a nonnegative interaction tilt the change of the mean
quadratic is nevertheless absolutely summable, with a bound given by
the squared Hilbert--Schmidt norm. No smooth spectral eigenfunctions,
finite rank, or additional trace-class assumption is imposed.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15e_recenter_scalar_abs_bound
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (γ : ℝ) (hγ : 0 ≤ γ) (j : ℕ) :
    |lam j * ((1 + γ * lam j)⁻¹ - 1)| ≤ γ * lam j ^ 2 := by
  have hl : 0 ≤ lam j := hlam j
  have hc : 0 ≤ γ * lam j := mul_nonneg hγ hl
  have hd : 0 < 1 + γ * lam j := by linarith
  have he : lam j * ((1 + γ * lam j)⁻¹ - 1) =
      -(γ * lam j ^ 2) / (1 + γ * lam j) := by
    field_simp
    ring
  rw [he, abs_div, abs_neg, abs_of_nonneg
    (mul_nonneg hγ (sq_nonneg _)), abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hγ (sq_nonneg (lam j))) hc]

theorem s15e_recenter_scalar_summable
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    Summable (fun j => lam j * ((1 + γ * lam j)⁻¹ - 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (hlam2.mul_left γ)
  simpa only [Real.norm_eq_abs] using
    s15e_recenter_scalar_abs_bound lam hlam γ hγ j

theorem s15e_finite_wick_recentering
    (lam : ℕ → ℝ) (ξ : ℕ → ℝ) (γ : ℝ) (n : ℕ) :
    (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, lam j * (ξ j ^ 2 - 1) =
    (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
      lam j * (ξ j ^ 2 - (1 + γ * lam j)⁻¹) +
    (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
      lam j * ((1 + γ * lam j)⁻¹ - 1) := by
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms s15e_recenter_scalar_abs_bound
#print axioms s15e_recenter_scalar_summable
#print axioms s15e_finite_wick_recentering
end HRS.MS.R26T3
