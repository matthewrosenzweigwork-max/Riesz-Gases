import HRS.MS.Fp81S21WeightedRellich9

/-!
The scaled cutoff remainder inherits one derivative constant for all radii.
This is the pointwise localization input; its conversion to the integrated
weighted Sobolev energy is a separate estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq
open scoped ContDiff

/-- Uniform pointwise derivative and support bounds for the exterior
remainder `f - χρ f`.  The same `C` controls cutoff derivatives for every
`ρ ≥ 1`; the remainder itself vanishes on the inner closed ball. -/
theorem fp81s21_weightedRellich_remainder_uniform
    {d q : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
    ∃ χ : Euc d → ℝ,
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
  obtain ⟨C, hC0, hCuniform⟩ :=
    fp81s21_weightedRellich_scaledCutoff_uniform (d := d) (q := q)
  refine ⟨C, hC0, ?_⟩
  intro ρ hρ f hf
  obtain ⟨χ, hχs, hχc, hχone, hχzero, hχB⟩ := hCuniform ρ hρ
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
  refine ⟨χ, hχs, hχc, hχone, hχzero, hC0, hrem, htsupp, ?_⟩
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

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_remainder_uniform

end HRS.Fp81.S21
