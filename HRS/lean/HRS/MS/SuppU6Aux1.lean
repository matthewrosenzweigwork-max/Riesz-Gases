import Mathlib

/-!
# U6 aux 1: the anisotropic affine charts `A x = 1 - γ(|x|²) x xᵀ` (radial scale `⟨x⟩⁻¹`)

`A x` is symmetric, `‖A x‖ ≤ 1`, has inverse `B x = 1 + δ(|x|²) x xᵀ`, `‖B x v‖² = ‖v‖² + ⟪x,v⟫²`,
`A x x = x/⟨x⟩` and `det (A x) = ⟨x⟩⁻¹`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace HRS.U6

section Alg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `w(s) = √(1+s)`. -/
def u6w (s : ℝ) : ℝ := Real.sqrt (1 + s)

/-- `γ(s) = 1/(w(1+w))`. -/
def u6g (s : ℝ) : ℝ := 1 / (u6w s * (1 + u6w s))

/-- `δ(s) = 1/(1+w)`. -/
def u6d (s : ℝ) : ℝ := 1 / (1 + u6w s)

lemma u6w_one_le {s : ℝ} (hs : 0 ≤ s) : 1 ≤ u6w s := by
  unfold u6w
  exact Real.one_le_sqrt.mpr (by linarith)

lemma u6w_sq {s : ℝ} (hs : 0 ≤ s) : u6w s ^ 2 = 1 + s := by
  unfold u6w
  rw [Real.sq_sqrt (by linarith)]

/-- The rank-one map `v ↦ ⟪x,v⟫ x`. -/
def u6P (x : E) : E →L[ℝ] E := (innerSL ℝ x).smulRight x

lemma u6P_apply (x v : E) : u6P x v = ⟪x, v⟫ • x := by
  simp [u6P]

/-- The chart matrix `A x = 1 - γ(|x|²) x xᵀ`. -/
def u6A (x : E) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - u6g (‖x‖ ^ 2) • u6P x

/-- The inverse chart matrix `B x = 1 + δ(|x|²) x xᵀ`. -/
def u6B (x : E) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + u6d (‖x‖ ^ 2) • u6P x

lemma u6A_apply (x v : E) : u6A x v = v - (u6g (‖x‖ ^ 2) * ⟪x, v⟫) • x := by
  simp [u6A, u6P_apply, sub_eq_add_neg, mul_smul]

lemma u6B_apply (x v : E) : u6B x v = v + (u6d (‖x‖ ^ 2) * ⟪x, v⟫) • x := by
  simp [u6B, u6P_apply, mul_smul]

/-- Scalar identities among `w, γ, δ`. -/
lemma u6_scalar (x : E) :
    let w := u6w (‖x‖ ^ 2)
    1 ≤ w ∧ ‖x‖ ^ 2 = w ^ 2 - 1 ∧ u6d (‖x‖ ^ 2) = 1 / (1 + w) ∧
      u6g (‖x‖ ^ 2) = 1 / (w * (1 + w)) := by
  intro w
  have h0 : 0 ≤ ‖x‖ ^ 2 := by positivity
  refine ⟨u6w_one_le h0, ?_, rfl, rfl⟩
  have := u6w_sq h0
  linarith

lemma u6A_B (x v : E) : u6A x (u6B x v) = v := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  rw [u6A_apply, u6B_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have e : u6g (‖x‖ ^ 2) * (⟪x, v⟫ + u6d (‖x‖ ^ 2) * ⟪x, v⟫ * ‖x‖ ^ 2) =
      u6d (‖x‖ ^ 2) * ⟪x, v⟫ := by
    set w := u6w (‖x‖ ^ 2)
    rw [hd, hg, hs]
    have hw0 : 0 < w := by linarith
    have hw1 : 0 < 1 + w := by linarith
    field_simp
    ring
  have e2 : (u6g (‖x‖ ^ 2) * (⟪x, v⟫ + u6d (‖x‖ ^ 2) * ⟪x, v⟫ * ‖x‖ ^ 2)) • x =
      (u6d (‖x‖ ^ 2) * ⟪x, v⟫) • x := by rw [e]
  rw [e2]; abel

lemma u6B_A (x v : E) : u6B x (u6A x v) = v := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  rw [u6B_apply, u6A_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have e : u6d (‖x‖ ^ 2) * (⟪x, v⟫ - u6g (‖x‖ ^ 2) * ⟪x, v⟫ * ‖x‖ ^ 2) =
      u6g (‖x‖ ^ 2) * ⟪x, v⟫ := by
    set w := u6w (‖x‖ ^ 2)
    rw [hd, hg, hs]
    have hw0 : 0 < w := by linarith
    have hw1 : 0 < 1 + w := by linarith
    field_simp
    ring
  rw [e]; abel

lemma norm_u6B_sq (x v : E) : ‖u6B x v‖ ^ 2 = ‖v‖ ^ 2 + ⟪x, v⟫ ^ 2 := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  set w := u6w (‖x‖ ^ 2)
  rw [u6B_apply, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x v]
  simp only [conj_trivial]
  rw [hd, hs]
  have hw0 : 0 < w := by linarith
  have hw1 : 0 < 1 + w := by linarith
  field_simp
  ring

lemma norm_u6A_sq (x v : E) :
    ‖u6A x v‖ ^ 2 = ‖v‖ ^ 2 - (2 * u6g (‖x‖ ^ 2) - u6g (‖x‖ ^ 2) ^ 2 * ‖x‖ ^ 2) * ⟪x, v⟫ ^ 2 := by
  rw [u6A_apply, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x v]
  simp only [conj_trivial]
  rw [← real_inner_self_eq_norm_sq]
  simp only [real_inner_self_eq_norm_sq]
  ring

lemma u6g_nonneg_coef (x : E) :
    0 ≤ 2 * u6g (‖x‖ ^ 2) - u6g (‖x‖ ^ 2) ^ 2 * ‖x‖ ^ 2 := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  set w := u6w (‖x‖ ^ 2)
  rw [hg, hs]
  have hw0 : 0 < w := by linarith
  have hw1 : 0 < 1 + w := by linarith
  have : 2 * (1 / (w * (1 + w))) - (1 / (w * (1 + w))) ^ 2 * (w ^ 2 - 1) =
      (w + 1) / (w ^ 2 * (1 + w)) * 1 + 0 := by
    field_simp
    ring
  rw [this]
  positivity

lemma norm_u6A_le (x v : E) : ‖u6A x v‖ ≤ ‖v‖ := by
  have h := norm_u6A_sq x v
  have h2 := u6g_nonneg_coef x
  have : ‖u6A x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg ⟪x, v⟫, mul_nonneg h2 (sq_nonneg ⟪x, v⟫)]
  exact le_of_sq_le_sq this (norm_nonneg _) |>.trans_eq rfl

lemma opNorm_u6A_le (x : E) : ‖u6A x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simpa using norm_u6A_le x v)

lemma inner_u6A (x y v : E) : ⟪y, u6A x v⟫ = ⟪u6A x y, v⟫ := by
  rw [u6A_apply, u6A_apply]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_comm x v, real_inner_comm x y]
  simp only [conj_trivial]
  ring

lemma u6A_self (x : E) : u6A x x = (1 / u6w (‖x‖ ^ 2)) • x := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  set w := u6w (‖x‖ ^ 2)
  rw [u6A_apply, real_inner_self_eq_norm_sq, hg, hs]
  have hw0 : 0 < w := by linarith
  have hw1 : 0 < 1 + w := by linarith
  have : 1 - 1 / (w * (1 + w)) * (w ^ 2 - 1) = 1 / w := by
    field_simp
    ring
  rw [← this, sub_smul, one_smul, mul_comm (1 / (w * (1 + w)))]

lemma norm_u6A_self_le (x : E) : ‖u6A x x‖ ≤ 1 := by
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  set w := u6w (‖x‖ ^ 2)
  rw [u6A_self, norm_smul, norm_div, norm_one, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ w)]
  have h1 : ‖x‖ ≤ w := by
    have : ‖x‖ ^ 2 ≤ w ^ 2 := by rw [hs]; linarith
    exact le_of_sq_le_sq this (by linarith)
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
  exact h1

end Alg

section Det

variable {d : ℕ}

lemma u6_det (x : EuclideanSpace ℝ (Fin d)) :
    LinearMap.det (u6A x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      1 / u6w (‖x‖ ^ 2) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (u6A x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin d)) =
      1 + Matrix.replicateCol (Fin 1) (fun i => -(u6g (‖x‖ ^ 2) * x i)) *
        Matrix.replicateRow (Fin 1) (fun j => x j) := by
    ext i j
    simp [LinearMap.toMatrix_apply, u6A_apply, Matrix.one_apply, Matrix.mul_apply,
      EuclideanSpace.inner_single_right]
    ring
  rw [hm]
  refine (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (fun i => -(u6g (‖x‖ ^ 2) * x i)) (fun j => x j)).trans ?_
  obtain ⟨hw, hs, hd, hg⟩ := u6_scalar x
  set w := u6w (‖x‖ ^ 2)
  have : (fun j => x j) ⬝ᵥ (fun i => -(u6g (‖x‖ ^ 2) * x i)) = -(u6g (‖x‖ ^ 2) * ‖x‖ ^ 2) := by
    have h2 : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; simp
    generalize u6g (‖x‖ ^ 2) = g
    rw [h2]
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, hg, hs]
  have hw0 : 0 < w := by linarith
  have hw1 : 0 < 1 + w := by linarith
  field_simp
  ring

end Det

end HRS.U6
