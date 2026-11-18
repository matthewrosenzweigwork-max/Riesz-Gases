import HRS.Commutator.Torus.NRSTAux7

/-!
# NRS-T, part 8: the bound for real trigonometric polynomials, conditional on the base and multiplier bounds
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

lemma rieszCoeff_eq_lw (s : ℝ) {k : Lattice d} (hk : k ≠ 0) :
    rieszCoeff d s k = rieszConst d s * lw (s - d) k := by
  unfold rieszCoeff lw
  rw [if_neg hk, if_neg hk]

/-- `Λ^{d-s}(g * A) = c₀ A` for mean-free `A`. -/
lemma lam_Rg (s : ℝ) (A : TPA d) (hA0 : A.coeff 0 = 0) :
    lam ((d : ℝ) - s) (Rg d s A) = (rieszConst d s : ℂ) • A := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  rw [coeff_lam, coeff_Rg, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hk : k = 0
  · subst hk; simp [hA0]
  · rw [rieszCoeff_eq_lw s hk]
    have : lw ((d : ℝ) - s) k * (rieszConst d s * lw (s - d) k) = rieszConst d s := by
      have h1 : lw ((d : ℝ) - s) k * lw (s - d) k = 1 := by
        rw [← lw_mul]
        have : ((d : ℝ) - s) + (s - d) = 0 := by ring
        rw [this]
        unfold lw; rw [if_neg hk, Real.rpow_zero]
      linear_combination (rieszConst d s) * h1
    rw [← mul_assoc, show ((lw ((d : ℝ) - s) k : ℝ) : ℂ) * ((rieszConst d s * lw (s - d) k : ℝ) : ℂ) * A.coeff k =
        ((lw ((d : ℝ) - s) k * (rieszConst d s * lw (s - d) k) : ℝ) : ℂ) * A.coeff k by push_cast; ring, this]

lemma hom_Rg (s : ℝ) (A : TPA d) :
    hom (((d : ℝ) - s) / 2) (Rg d s A) = rieszConst d s ^ 2 * hom (-(((d : ℝ) - s) / 2)) A := by
  rw [hom_eq_sum _ (Rg d s A) (supp_Rg_subset s A), hom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_Rg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hk : k = 0
  · simp [hk, lw_zero]
  · rw [rieszCoeff_eq_lw s hk, abs_mul, abs_of_nonneg (lw_nonneg _ _)]
    have h1 : lw (((d : ℝ) - s) / 2) k * lw (s - d) k = lw (-(((d : ℝ) - s) / 2)) k := by
      rw [← lw_mul]; congr 1; ring
    have : lw (((d : ℝ) - s) / 2) k * (|rieszConst d s| * lw (s - d) k) =
        |rieszConst d s| * lw (-(((d : ℝ) - s) / 2)) k := by
      rw [← h1]; ring
    calc lw (((d : ℝ) - s) / 2) k ^ 2 * (|rieszConst d s| * lw (s - d) k * ‖A.coeff k‖) ^ 2
        = (lw (((d : ℝ) - s) / 2) k * (|rieszConst d s| * lw (s - d) k) * ‖A.coeff k‖) ^ 2 := by ring
      _ = rieszConst d s ^ 2 * (lw (-(((d : ℝ) - s) / 2)) k ^ 2 * ‖A.coeff k‖ ^ 2) := by
        rw [this, mul_pow, mul_pow, sq_abs]; ring

end HRS.Commutator.TorusNote.NRST
