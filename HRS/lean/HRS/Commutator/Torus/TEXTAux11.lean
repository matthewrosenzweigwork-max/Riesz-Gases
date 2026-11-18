import HRS.Commutator.Torus.TEXTAux10

/-!
# T-EXT-A helpers, part 11: real trigonometric polynomials with prescribed even coefficients
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_cos_cast (k : Lattice d) (x : Torus d) :
    ((Torus.cosMode k x : ℝ) : ℂ) = (Torus.mode k x + Torus.mode (-k) x) / 2 := by
  unfold Torus.cosMode
  rw [Complex.re_eq_add_conj, Torus.mode_neg]

lemma text_trigpoly (p : Lattice d → ℝ) (S : Finset (Lattice d)) (hS : ∀ k, p k ≠ 0 → k ∈ S)
    (hev : ∀ k, p (-k) = p k) :
    ∃ P : Torus d → ℝ, Continuous P ∧ ∀ l : Lattice d, Torus.fcoef P l = ((p l : ℝ) : ℂ) := by
  classical
  refine ⟨fun x => ∑ k ∈ S, p k * Torus.cosMode k x, ?_, fun l => ?_⟩
  · exact continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_cosMode k)
  · unfold Torus.fcoef
    have h1 : ∀ x : Torus d, Torus.mode (-l) x * (((∑ k ∈ S, p k * Torus.cosMode k x : ℝ)) : ℂ) =
        ∑ k ∈ S, ((p k : ℂ) / 2) * (Torus.mode (-l) x * Torus.mode k x +
          Torus.mode (-l) x * Torus.mode (-k) x) := by
      intro x
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [text_cos_cast]
      ring
    simp_rw [h1]
    rw [integral_finset_sum]
    · have h2 : ∀ k ∈ S, ∫ x : Torus d, ((p k : ℂ) / 2) * (Torus.mode (-l) x * Torus.mode k x +
          Torus.mode (-l) x * Torus.mode (-k) x) =
          ((p k : ℂ) / 2) * ((if -l + k = 0 then 1 else 0) + (if -l + -k = 0 then 1 else 0)) := by
        intro k _
        rw [integral_const_mul, integral_add (Torus.integrable_mode_mul _ _)
          (Torus.integrable_mode_mul _ _), Torus.integral_mode_mul, Torus.integral_mode_mul]
      rw [Finset.sum_congr rfl h2]
      have h3 : ∀ k : Lattice d, (-l + k = 0) ↔ (l = k) := fun k => neg_add_eq_zero
      have e : ∀ x : Lattice d, (l = -x) ↔ (-l = x) := fun x => by
        constructor
        · intro h; rw [h, neg_neg]
        · intro h; rw [← h, neg_neg]
      simp only [h3, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, e]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
      by_cases hl : p l = 0
      · have hl' : p (-l) = 0 := by rw [hev, hl]
        simp [hl, hl']
      · have h5 : l ∈ S := hS l hl
        have h6 : -l ∈ S := hS (-l) (by rw [hev]; exact hl)
        rw [if_pos h5, if_pos h6, hev]
        push_cast
        ring
    · intro k _
      exact (((Torus.integrable_mode_mul _ _).add (Torus.integrable_mode_mul _ _))).const_mul _

end HRS.Commutator.TorusNote
