import HRS.MC.E213U18a
import HRS.Prob.Gaussian

/-!
# E214C (part 1): polarization

If a symmetric tensor `D ∈ TensorDual B 3` kills all cubes `trilin ![L, L, L]`, then it kills every
product `trilin ![l₁, l₂, l₃]`.
-/

noncomputable section

namespace HRS.MC.E214C

open HRS HRS.MC.E213U18

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

section Lin

variable (D : TensorDual B 3)

/-- The trilinear function `T(a,b,c) = D (trilin ![a,b,c])` on functionals. -/
def Tf (a b c : StrongDual ℝ B) : ℝ := D (trilin ![a, b, c])

theorem Tf_add1 (x x' y z : StrongDual ℝ B) : Tf D (x + x') y z = Tf D x y z + Tf D x' y z := by
  unfold Tf
  rw [← map_add]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.add_apply]
  simp; ring

theorem Tf_add2 (x y y' z : StrongDual ℝ B) : Tf D x (y + y') z = Tf D x y z + Tf D x y' z := by
  unfold Tf
  rw [← map_add]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.add_apply]
  simp; ring

theorem Tf_add3 (x y z z' : StrongDual ℝ B) : Tf D x y (z + z') = Tf D x y z + Tf D x y z' := by
  unfold Tf
  rw [← map_add]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.add_apply]
  simp; ring

theorem Tf_neg1 (x y z : StrongDual ℝ B) : Tf D (-x) y z = - Tf D x y z := by
  unfold Tf
  rw [← map_neg]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.neg_apply]
  simp

theorem Tf_neg2 (x y z : StrongDual ℝ B) : Tf D x (-y) z = - Tf D x y z := by
  unfold Tf
  rw [← map_neg]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.neg_apply]
  simp

theorem Tf_neg3 (x y z : StrongDual ℝ B) : Tf D x y (-z) = - Tf D x y z := by
  unfold Tf
  rw [← map_neg]; congr 1
  ext v; simp only [trilin_apply, ContinuousMultilinearMap.neg_apply]
  simp

end Lin

/-- The six permuted values of a symmetric `D` sum to `6 T(a,b,c)`. -/
theorem Tf_six_of_symm (D : TensorDual B 3)
    (hsym : ∀ (M : B [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)), D (M.domDomCongr σ) = D M)
    (a b c : StrongDual ℝ B) :
    Tf D a b c + Tf D a c b + Tf D b a c + Tf D b c a + Tf D c a b + Tf D c b a =
      6 * Tf D a b c := by
  have h := sum_perm_trilin D ![a, b, c]
  simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial, nsmul_eq_mul] at h
  have e : ((3 : ℕ) * (2 * (1 * 1)) : ℝ) = 6 := by norm_num
  simp at h
  unfold Tf
  push_cast at h
  linarith

/-- Polarization: a symmetric `D` vanishing on all cubes `trilin ![L, L, L]` vanishes on every
`trilin ![l₁, l₂, l₃]`. -/
theorem e214_prod_zero_of_cubes (D : TensorDual B 3)
    (hsym : ∀ (M : B [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)), D (M.domDomCongr σ) = D M)
    (hcube : ∀ L : StrongDual ℝ B, D (trilin ![L, L, L]) = 0) (a b c : StrongDual ℝ B) :
    D (trilin ![a, b, c]) = 0 := by
  have h6 := Tf_six_of_symm D hsym a b c
  have c1 := hcube (a + b + c)
  have c2 := hcube (a + b + -c)
  have c3 := hcube (a + -b + c)
  have c4 := hcube (a + -b + -c)
  have c5 := hcube (-a + b + c)
  have c6 := hcube (-a + b + -c)
  have c7 := hcube (-a + -b + c)
  have c8 := hcube (-a + -b + -c)
  change Tf D _ _ _ = 0 at c1 c2 c3 c4 c5 c6 c7 c8
  simp only [Tf_add1, Tf_add2, Tf_add3, Tf_neg1, Tf_neg2, Tf_neg3] at c1 c2 c3 c4 c5 c6 c7 c8
  change Tf D a b c = 0
  linarith

end HRS.MC.E214C
