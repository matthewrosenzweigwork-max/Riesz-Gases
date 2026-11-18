import HRS.MS.Fp81S21WeightedRellich7

/-!
The scaled cutoff has uniformly bounded ordered derivatives.  This file
records the resulting iterated Leibniz estimate for its product with a test.
It is a pointwise derivative estimate; converting it into the integrated
weighted source-norm bound needed for the global compactness argument remains
separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq
open scoped ContDiff

/-- Iterated product-rule bound for a smooth multiplier with derivatives
bounded by C through order q + 2.  Each summand is one Leibniz term, with
the binomial coefficient for distributing the ordered derivatives.
-/
theorem fp81s21_weightedRellich_productDerivative_bound
    {d q : ℕ} {χ f : Euc d → ℝ} {C : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C)
    (hχB : ∀ k ≤ q + 2, ∀ x,
      ‖iteratedFDeriv ℝ k χ x‖ ≤ C) :
    ∀ j ≤ q + 2, ∀ i : Fin j → Fin d, ∀ x,
      |partialDeriv i (fun y => χ y * f y) x| ≤
        ∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) * (C * ‖iteratedFDeriv ℝ (j - k) f x‖) := by
  intro j hj i x
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := χ) (g := f)
    (N := ((q + 2 : ℕ) : WithTop ℕ∞))
    (hχ.of_le (by simp))
    (hf.of_le (by simp)) x (n := j) (by exact_mod_cast hj)
  have hpartial :
      |partialDeriv i (fun y => χ y * f y) x| ≤
        ‖iteratedFDeriv ℝ j (fun y => χ y * f y) x‖ :=
    s57p_abs_partialDeriv_le i (fun y => χ y * f y) x
  refine hpartial.trans (hmul.trans ?_)
  apply Finset.sum_le_sum
  intro k hk
  have hkj : k ≤ j := by
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hχk : ‖iteratedFDeriv ℝ k χ x‖ ≤ C :=
    hχB k (hkj.trans hj) x
  have hprod :
      ‖iteratedFDeriv ℝ k χ x‖ *
        ‖iteratedFDeriv ℝ (j - k) f x‖ ≤
      C * ‖iteratedFDeriv ℝ (j - k) f x‖ :=
    mul_le_mul_of_nonneg_right hχk (norm_nonneg _)
  calc
    (j.choose k : ℝ) * ‖iteratedFDeriv ℝ k χ x‖ *
        ‖iteratedFDeriv ℝ (j - k) f x‖
      = (j.choose k : ℝ) *
        (‖iteratedFDeriv ℝ k χ x‖ *
          ‖iteratedFDeriv ℝ (j - k) f x‖) := by ring
    _ ≤ (j.choose k : ℝ) *
        (C * ‖iteratedFDeriv ℝ (j - k) f x‖) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Combining the scaled cutoff with the product rule gives compactly
supported localized tests and an explicit, radius-independent pointwise
Leibniz bound for every ordered derivative through q + 2.
-/
theorem fp81s21_weightedRellich_scaledCutoff_productDerivative_bound
    {d q : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) (f : Euc d → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∃ χ : Euc d → ℝ, ∃ C : ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
      (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
      0 ≤ C ∧
      (∀ j ≤ q + 2, ∀ i : Fin j → Fin d, ∀ x,
        |partialDeriv i (fun y => χ y * f y) x| ≤
          ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) *
              (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) := by
  obtain ⟨χ, hχs, hχc, hχone, hχzero, C, hC0, hχB⟩ :=
    fp81s21_weightedRellich_scaledCutoff (d := d) (q := q) hρ
  refine ⟨χ, C, hχs, hχc, hχone, hχzero, hC0, ?_⟩
  exact fp81s21_weightedRellich_productDerivative_bound hχs hf hC0 hχB

/-- The exterior remainder is zero on the inner ball, has thick support in
the closed exterior region, and its ordered derivatives satisfy the
pointwise product-rule bound.  This localizes the remainder before the
integrated weighted tail estimate is applied.
-/
theorem fp81s21_weightedRellich_scaledCutoff_remainder_bound
    {d q : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) (f : Euc d → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∃ χ : Euc d → ℝ, ∃ C : ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
      (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
      0 ≤ C ∧
      (∀ x, ‖x‖ ≤ ρ → f x - χ x * f x = 0) ∧
      tsupport (fun x => f x - χ x * f x) ⊆ {x | ρ ≤ ‖x‖} ∧
      (∀ j ≤ q + 2, ∀ i : Fin j → Fin d, ∀ x,
        |partialDeriv i (fun y => f y - χ y * f y) x| ≤
          |partialDeriv i f x| +
            ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) *
                (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) := by
  obtain ⟨χ, hχs, hχc, hχone, hχzero, C, hC0, hχB⟩ :=
    fp81s21_weightedRellich_scaledCutoff (d := d) (q := q) hρ
  have hprod := fp81s21_weightedRellich_productDerivative_bound
    hχs hf hC0 hχB
  have hrem : ∀ x, ‖x‖ ≤ ρ → f x - χ x * f x = 0 := by
    intro x hx
    rw [hχone x hx]
    ring
  have htsupp :
      tsupport (fun x => f x - χ x * f x) ⊆ {x | ρ ≤ ‖x‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro x hx
    by_contra hxρ
    apply Function.mem_support.1 hx
    have hzero := hrem x (le_of_not_ge hxρ)
    simpa [hzero]
  refine ⟨χ, C, hχs, hχc, hχone, hχzero, hC0, hrem, htsupp, ?_⟩
  intro j hj i x
  have hf' : ContDiff ℝ (q + 2) f := hf.of_le (by simp)
  have hχf : ContDiff ℝ (q + 2) (fun y => χ y * f y) :=
    (hχs.mul hf).of_le (by simp)
  have hsub := s57p_partialDeriv_sub hf' hχf hj i x
  have htriangle :
      |partialDeriv i f x - partialDeriv i (fun y => χ y * f y) x| ≤
        |partialDeriv i f x| +
          |partialDeriv i (fun y => χ y * f y) x| := by
    simpa only [Real.norm_eq_abs] using
      (norm_sub_le (partialDeriv i f x)
        (partialDeriv i (fun y => χ y * f y) x))
  rw [hsub]
  calc
    |partialDeriv i f x - partialDeriv i (fun y => χ y * f y) x|
      ≤ |partialDeriv i f x| +
          |partialDeriv i (fun y => χ y * f y) x| := htriangle
    _ ≤ |partialDeriv i f x| +
          ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) *
              (C * ‖iteratedFDeriv ℝ (j - k) f x‖) :=
      add_le_add le_rfl (hprod j hj i x)

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_productDerivative_bound
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_scaledCutoff_productDerivative_bound
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_scaledCutoff_remainder_bound

end HRS.Fp81.S21
