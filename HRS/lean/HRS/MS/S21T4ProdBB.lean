import HRS.MS.S21T4ProdBA
import HRS.MS.S21T4ProdAU

/-! A finite-family Euclidean inner-product identity for R26-T3.S13. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21t4_finappend_inner {n m : ℕ}
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (t : EuclideanSpace ℝ (Fin (n + m))) :
    inner ℝ (WithLp.toLp 2 (Fin.append a b) :
      EuclideanSpace ℝ (Fin (n + m))) t =
      (∑ i : Fin n, t (Fin.castAdd m i) * a i) +
      (∑ k : Fin m, t (Fin.natAdd n k) * b k) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.append_left]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Fin.append_right]

end HRS.MS.R26T3
