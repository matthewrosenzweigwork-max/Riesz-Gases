import HRS.Prob.Gaussian

/-!
# Isonormal Gaussian processes: basis independence of the quadratic chaos (Proposition 7.18)

Statement only (the theorem ends in `sorry`); relocated from `HRS/SA/Drafts/SAD1.lean` after the independent review
recorded in `docs/ISSUES.md` and subsequent approval.  TeX L9829-9835: "Finite-dimensional orthogonal changes of basis preserve
the centered quadratic polynomial.  Approximation then gives its basis-independent meaning for an isonormal Gaussian
process, with the process transformed along with the basis."  `HRS.chaos_basis_independent` covers only orthogonal changes
of finitely many coordinates.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS

section Isonormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω]

/-- An isonormal Gaussian process on the real Hilbert space `H`: `W h` are random variables whose finite
families are centred Gaussian vectors with covariance the Gram matrix `⟪h_i, h_j⟫` (`W` is then a.e. linear). -/
def IsIsonormal (P : Measure Ω) (W : H → Ω → ℝ) : Prop :=
  ∀ (n : ℕ) (h : Fin n → H),
    law P (fun ω => (WithLp.toLp 2 fun i : Fin n => W (h i) ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j))

/-- The finite sections `½ ∑_{i,j<L} ⟪e_i, A e_j⟫ (W(e_i) W(e_j) - δ_{ij})` of the centred quadratic chaos of the
operator `A`, computed in the basis `e`. -/
def isoSection (A : H →L[ℝ] H) (W : H → Ω → ℝ) (e : ℕ → H) (L : ℕ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    inner ℝ (e i) (A (e j)) * (W (e i) ω * W (e j) ω - if i = j then 1 else 0)

/-- (b3) Proposition 7.18, "has a basis-independent Gaussian quadratic-chaos meaning" (TeX L9829-9835: "Finite-dimensional
orthogonal changes of basis preserve the centered quadratic polynomial.  Approximation then gives its basis-independent
meaning for an isonormal Gaussian process, with the process transformed along with the basis"): let `A` be a
symmetric Hilbert-Schmidt operator on a (separable) real Hilbert space, `W` an isonormal Gaussian process, and `e, e'` two
orthonormal bases (Hilbert bases indexed by `ℕ`).  If `A` is Hilbert-Schmidt in the basis `e` (`∑‖A e_i‖² < ∞`;
this is basis independent), then the sections computed in `e` and in `e'` converge in `L²(P)` to one and the same
limit `Q`. -/
theorem chaos_isonormal_basis_independent [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H → Ω → ℝ) (hW : IsIsonormal P W)
    (A : H →L[ℝ] H) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (e e' : HilbertBasis ℕ ℝ H) (hHS : Summable fun i => ‖A (e i)‖ ^ 2) :
    ∃ Q : Ω → ℝ, HRS.TendstoL2 P (isoSection A W e) Q ∧ HRS.TendstoL2 P (isoSection A W e') Q := by
  sorry

end Isonormal

end HRS
