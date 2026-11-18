import HRS.MS.S111K4D

/-!
# S11.1 / T01 (S11K4), part E: the finite Wick difference of two jointly Gaussian families

For a centered Gaussian vector `X = (z, z')` indexed by `Fin 2 × Fin n` with the operator-norm hypotheses on `z`, `z'`
and `z - z'`, the difference of the two centered quadratic forms with the same matrix `A` has second moment at most
`8 B² δ² ‖A‖²_F` (Pro `R26-T6.W03`/`W04`; the exact chaos factor is `vGauss = 2`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HRS.MS.S111K4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem k4_linear_mul (a b : ι → ℝ) :
    ∫ y, (∑ k, a k * y k) * (∑ k, b k * y k) ∂(k4gm ι) = ∑ k, a k * b k := by
  have e : ∀ y : ι → ℝ, (∑ k, a k * y k) * (∑ k, b k * y k) = ∑ k, ∑ l, (a k * b l) * (y k * y l) := fun y => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (k4_integrable_coord_mul k l).const_mul _]
  have : ∀ k ∈ (Finset.univ : Finset ι), ∫ y, ∑ l, (a k * b l) * (y k * y l) ∂(k4gm ι) = a k * b k := by
    intro k _
    rw [integral_finsetSum _ fun l _ => (k4_integrable_coord_mul k l).const_mul _]
    simp_rw [integral_const_mul, k4_second_moment]
    simp
  rw [Finset.sum_congr rfl this]

variable {n : Type*} [Fintype n]

theorem k4_quad_expand (S : Matrix ι n ℝ) (A : Matrix n n ℝ) (g : ι → ℝ) :
    ∑ i, ∑ j, A i j * ((∑ k, S k i * g k) * (∑ l, S l j * g l)) = g ⬝ᵥ ((S * A * Sᵀ).mulVec g) := by
  have hu : ∀ i, (Sᵀ.mulVec g) i = ∑ k, S k i * g k := fun i => by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec, ← hu]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem k4_trace_expand (S : Matrix ι n ℝ) (A : Matrix n n ℝ) :
    ∑ i, ∑ j, A i j * ∑ k, S k i * S k j = (S * A * Sᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc ∑ x, ∑ y, ∑ i, A x y * (S i x * S i y)
      = ∑ x, ∑ i, ∑ y, A x y * (S i x * S i y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, A x y * (S i x * S i y) := Finset.sum_comm
    _ = ∑ i, ∑ y, ∑ x, A x y * (S i x * S i y) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun x _ => by ring

end HRS.MS.S111K4
