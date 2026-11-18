import HRS.MS.R26T8AL3a

/-!
# S8.2 observed-time layer, generic lemma L3b: Leibniz rule for pure directional iterates

`D^[j] (c · v) = ∑_{k ≤ j} C(j,k) (D^[k] c) (D^[j-k] v)` for smooth `c, v`, where `D = ∂_{e_i}`.
Route: Pascal's rule for the sequence of real coefficients, then induction on `j` with the product rule.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_l3_contDiff_D (i : Fin d) (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (r26t8a_l3_D i f) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

theorem r26t8a_l3_contDiff_iter (i : Fin d) (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ ((r26t8a_l3_D i)^[k] f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact r26t8a_l3_contDiff_D i _ ih

/-- Pascal-type identity for the Leibniz coefficients. -/
theorem r26t8a_l3_pascal (a b : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a (k + 1) * b (j - k) + a k * b (j - k + 1)) =
      ∑ k ∈ Finset.range (j + 2), ((j + 1).choose k : ℝ) * (a k * b (j + 1 - k)) := by
  have h1 : ∑ k ∈ Finset.range (j + 2), ((j + 1).choose k : ℝ) * (a k * b (j + 1 - k)) =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a (k + 1) * b (j - k)) +
      ∑ k ∈ Finset.range (j + 1), (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j - k)) +
      a 0 * b (j + 1) := by
    rw [Finset.sum_range_succ']
    have e : ∀ k ∈ Finset.range (j + 1), ((j + 1).choose (k + 1) : ℝ) * (a (k + 1) * b (j + 1 - (k + 1))) =
        (j.choose k : ℝ) * (a (k + 1) * b (j - k)) + (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j - k)) := by
      intro k _
      have : j + 1 - (k + 1) = j - k := by omega
      rw [this, Nat.choose_succ_succ]
      push_cast
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]
  have h2 : ∑ k ∈ Finset.range (j + 1), (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j - k)) +
      a 0 * b (j + 1) =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a k * b (j + 1 - k)) := by
    rw [Finset.sum_range_succ' (fun k => (j.choose k : ℝ) * (a k * b (j + 1 - k))),
      Finset.sum_range_succ (fun k => (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j - k)))]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self j)]
    have e2 : ∑ k ∈ Finset.range j, (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j - k)) =
        ∑ k ∈ Finset.range j, (j.choose (k + 1) : ℝ) * (a (k + 1) * b (j + 1 - (k + 1))) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < j := Finset.mem_range.1 hk
      have : j - k = j + 1 - (k + 1) := by omega
      rw [this]
    rw [e2]
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.sub_zero]
  have hsplit : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a (k + 1) * b (j - k) + a k * b (j - k + 1)) =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a (k + 1) * b (j - k)) +
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (a k * b (j + 1 - k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < j + 1 := Finset.mem_range.1 hk
    have : j - k + 1 = j + 1 - k := by omega
    rw [this]
    ring
  rw [hsplit, h1, add_assoc, h2]

end HRS.MS.R26T8A
end
