import Mathlib

/-!
# C-STE, part 2: the Jacobian of the cone parametrisation of the stereographic projection

On `E = Fin (d+1) → ℝ` write `z = (x, s)` with `x = (z_0, …, z_{d-1})`, `s = z_d`, and `Q(z) = |x|²`.
The map `G(z) = s · (2x, |x|² - 1)` is the composition `H ∘ P` of
* `P(z) = (s x, s)`, with upper triangular Jacobian of determinant `s^d`;
* `H(z) = (2 z', Q(z)/z_d - z_d)`, with lower triangular Jacobian of determinant
  `-2^d (Q(z)/z_d² + 1)` (for `z_d ≠ 0`).
Hence `|det G'(z)| = (2s)^d (1 + |x|²)` for `s > 0`, and `G` is injective on `{s > 0}`.
-/

noncomputable section

namespace HRS.MS.Thm

variable {d : ℕ}

/-- `P(z) = (s x, s)`. -/
def stePmap (z : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun i => if i = Fin.last d then z (Fin.last d) else z (Fin.last d) * z i

/-- `Q(z) = |x|²`. -/
def steQ (z : Fin (d + 1) → ℝ) : ℝ := ∑ j : Fin d, z (Fin.castSucc j) ^ 2

/-- `H(z) = (2x, Q/s - s)`. -/
def steHmap (z : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun i => if i = Fin.last d then steQ z / z (Fin.last d) - z (Fin.last d) else 2 * z i

/-- `G = H ∘ P`. -/
def steG (z : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ := steHmap (stePmap z)

/-- Jacobian matrix of `P`. -/
def steMP (z : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => if i = Fin.last d then (if j = Fin.last d then 1 else 0)
    else if j = Fin.last d then z i else if i = j then z (Fin.last d) else 0

/-- Jacobian matrix of `H`. -/
def steMH (z : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => if i = Fin.last d then
      (if j = Fin.last d then -(steQ z / z (Fin.last d) ^ 2) - 1 else 2 * z j / z (Fin.last d))
    else if i = j then 2 else 0

/-- The continuous linear map of a matrix on `Fin (d+1) → ℝ`. -/
def steCLM (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

lemma steCLM_apply (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    steCLM M h i = ∑ j, M i j * h j := by
  simp [steCLM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

lemma ste_det_steCLM (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (steCLM M).det = M.det := by
  have : ((steCLM M : (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ)) :
      (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = Matrix.toLin' M := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_toLin']

lemma ste_det_MP (z : Fin (d + 1) → ℝ) : (steMP z).det = z (Fin.last d) ^ d := by
  have hU : (steMP z).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    have hj : j ≠ Fin.last d := (Fin.lt_last_iff_ne_last.mp (lt_of_lt_of_le hij' (Fin.le_last i)))
    by_cases hi : i = Fin.last d
    · simp [steMP, hi, hj]
    · simp [steMP, hi, hj, hij'.ne']
  rw [Matrix.det_of_isUpperTriangular hU, Fin.prod_univ_castSucc]
  simp [steMP, Fin.castSucc_ne_last]

lemma ste_det_MH (z : Fin (d + 1) → ℝ) :
    (steMH z).det = 2 ^ d * (-(steQ z / z (Fin.last d) ^ 2) - 1) := by
  have hL : (steMH z).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last d := (Fin.lt_last_iff_ne_last.mp (lt_of_lt_of_le hij' (Fin.le_last j)))
    simp [steMH, hi, hij'.ne]
  rw [Matrix.det_of_isLowerTriangular _ hL, Fin.prod_univ_castSucc]
  simp [steMH, Fin.castSucc_ne_last]

/-- The coordinate projection as a continuous linear map. -/
abbrev steProj (i : Fin (d + 1)) : (Fin (d + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

lemma ste_hasFDerivAt_coord (z : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    HasFDerivAt (fun w : Fin (d + 1) → ℝ => w i) (steProj i) z :=
  hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (d + 1) => ℝ) i z

lemma ste_hasFDerivAt_P (z : Fin (d + 1) → ℝ) : HasFDerivAt stePmap (steCLM (steMP z)) z := by
  rw [hasFDerivAt_pi']
  intro i
  by_cases hi : i = Fin.last d
  · subst hi
    have h1 : (fun w : Fin (d + 1) → ℝ => stePmap w (Fin.last d)) = fun w => w (Fin.last d) := by
      funext w; simp [stePmap]
    rw [h1]
    convert ste_hasFDerivAt_coord z (Fin.last d) using 1
    ext h
    simp [steCLM_apply, steMP, Fin.sum_univ_castSucc]
  · have h1 : (fun w : Fin (d + 1) → ℝ => stePmap w i) = fun w => w (Fin.last d) * w i := by
      funext w; simp [stePmap, hi]
    rw [h1]
    convert (ste_hasFDerivAt_coord z (Fin.last d)).mul (ste_hasFDerivAt_coord z i) using 1
    ext h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, steCLM_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Fintype.sum_eq_add (Fin.last d) i (Ne.symm hi)]
    · simp [steMP, hi]; ring
    · intro j hj
      simp [steMP, hi, hj.1, Ne.symm hj.2]

lemma ste_hasFDerivAt_Q (z : Fin (d + 1) → ℝ) :
    HasFDerivAt steQ (∑ j : Fin d, (2 * z (Fin.castSucc j)) • steProj (Fin.castSucc j)) z := by
  unfold steQ
  refine HasFDerivAt.fun_sum (fun j _ => ?_)
  have := (ste_hasFDerivAt_coord z (Fin.castSucc j)).pow 2
  convert this using 1
  simp

lemma ste_hasFDerivAt_H (z : Fin (d + 1) → ℝ) (hz : z (Fin.last d) ≠ 0) :
    HasFDerivAt steHmap (steCLM (steMH z)) z := by
  rw [hasFDerivAt_pi']
  intro i
  by_cases hi : i = Fin.last d
  · subst hi
    have h1 : (fun w : Fin (d + 1) → ℝ => steHmap w (Fin.last d)) =
        fun w => steQ w * (w (Fin.last d))⁻¹ - w (Fin.last d) := by
      funext w; simp [steHmap, div_eq_mul_inv]
    rw [h1]
    have hI : HasFDerivAt (fun w : Fin (d + 1) → ℝ => (w (Fin.last d))⁻¹)
        (-(z (Fin.last d) ^ 2)⁻¹ • steProj (Fin.last d)) z :=
      (hasDerivAt_inv hz).comp_hasFDerivAt z (ste_hasFDerivAt_coord z (Fin.last d))
    have := ((ste_hasFDerivAt_Q z).mul hI).sub (ste_hasFDerivAt_coord z (Fin.last d))
    convert this using 1
    ext h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, steCLM_apply]
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_add', Pi.sub_apply,
      Pi.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rw [Fin.sum_univ_castSucc]
    have hs : ∑ c : Fin d, steMH z (Fin.last d) (Fin.castSucc c) * h (Fin.castSucc c) =
        (z (Fin.last d))⁻¹ * ∑ c : Fin d, 2 * z (Fin.castSucc c) * h (Fin.castSucc c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [steMH, Fin.castSucc_ne_last]
      field_simp
    rw [hs]
    simp only [steMH, Matrix.of_apply, if_true]
    field_simp
    ring
  · have h1 : (fun w : Fin (d + 1) → ℝ => steHmap w i) = fun w => 2 * w i := by
      funext w; simp [steHmap, hi]
    rw [h1]
    convert (ste_hasFDerivAt_coord z i).const_mul (2 : ℝ) using 1
    ext h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, steCLM_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single i]
    · simp [steMH, hi]
    · intro j hj
      simp [steMH, hi, Ne.symm hj]

lemma steQ_P (z : Fin (d + 1) → ℝ) : steQ (stePmap z) = z (Fin.last d) ^ 2 * steQ z := by
  unfold steQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [stePmap, Fin.castSucc_ne_last]; ring

lemma steG_castSucc {z : Fin (d + 1) → ℝ} (hz : 0 < z (Fin.last d)) (j : Fin d) :
    steG z (Fin.castSucc j) = 2 * (z (Fin.last d) * z (Fin.castSucc j)) := by
  simp [steG, steHmap, stePmap, Fin.castSucc_ne_last]

lemma steG_last {z : Fin (d + 1) → ℝ} (hz : 0 < z (Fin.last d)) :
    steG z (Fin.last d) = z (Fin.last d) * steQ z - z (Fin.last d) := by
  have hs : z (Fin.last d) ≠ 0 := hz.ne'
  simp only [steG, steHmap, if_true, steQ_P]
  simp only [stePmap, if_true]
  field_simp

lemma ste_hasFDerivAt_G {z : Fin (d + 1) → ℝ} (hz : 0 < z (Fin.last d)) :
    HasFDerivAt steG ((steCLM (steMH (stePmap z))).comp (steCLM (steMP z))) z := by
  have hP := ste_hasFDerivAt_P z
  have hH := ste_hasFDerivAt_H (stePmap z) (by simpa [stePmap] using hz.ne')
  exact hH.comp z hP

lemma ste_abs_det_G {z : Fin (d + 1) → ℝ} (hz : 0 < z (Fin.last d)) :
    |((steCLM (steMH (stePmap z))).comp (steCLM (steMP z))).det| =
      (2 * z (Fin.last d)) ^ d * (1 + steQ z) := by
  have hs : z (Fin.last d) ≠ 0 := hz.ne'
  have h1 : ((steCLM (steMH (stePmap z))).comp (steCLM (steMP z))).det =
      (steCLM (steMH (stePmap z))).det * (steCLM (steMP z)).det := by
    simp only [ContinuousLinearMap.det]
    rw [← LinearMap.det_comp]; rfl
  rw [h1, ste_det_steCLM, ste_det_steCLM, ste_det_MH, ste_det_MP, steQ_P]
  have hl : stePmap z (Fin.last d) = z (Fin.last d) := by simp [stePmap]
  rw [hl]
  have : 2 ^ d * (-(z (Fin.last d) ^ 2 * steQ z / z (Fin.last d) ^ 2) - 1) * z (Fin.last d) ^ d =
      -((2 * z (Fin.last d)) ^ d * (1 + steQ z)) := by
    field_simp
    ring
  rw [this, abs_neg, abs_of_nonneg]
  have : 0 ≤ steQ z := Finset.sum_nonneg fun j _ => sq_nonneg _
  positivity

lemma steG_injOn : Set.InjOn (steG : (Fin (d + 1) → ℝ) → _) {z | 0 < z (Fin.last d)} := by
  intro z hz w hw hzw
  have hz : 0 < z (Fin.last d) := hz
  have hw : 0 < w (Fin.last d) := hw
  have hc : ∀ j : Fin d, z (Fin.last d) * z (Fin.castSucc j) = w (Fin.last d) * w (Fin.castSucc j) := by
    intro j
    have := congrFun hzw (Fin.castSucc j)
    rw [steG_castSucc hz, steG_castSucc hw] at this
    linarith
  have hl := congrFun hzw (Fin.last d)
  rw [steG_last hz, steG_last hw] at hl
  have hQ : z (Fin.last d) * steQ z = w (Fin.last d) * steQ w
      + (z (Fin.last d) - w (Fin.last d)) := by linarith
  -- `s ↦ s Q(z) - s` where `s² Q(z) = s'² Q(w)` forces `s = s'`
  have hsq : z (Fin.last d) ^ 2 * steQ z = w (Fin.last d) ^ 2 * steQ w := by
    unfold steQ
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hc j
    calc z (Fin.last d) ^ 2 * z (Fin.castSucc j) ^ 2
        = (z (Fin.last d) * z (Fin.castSucc j)) ^ 2 := by ring
      _ = (w (Fin.last d) * w (Fin.castSucc j)) ^ 2 := by rw [this]
      _ = _ := by ring
  have hs : z (Fin.last d) = w (Fin.last d) := by
    have hQ1 : 0 ≤ steQ w := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hprod : (z (Fin.last d) - w (Fin.last d)) * (w (Fin.last d) * steQ w + z (Fin.last d)) = 0 := by
      linear_combination hsq - z (Fin.last d) * hQ
    have hpos : 0 < w (Fin.last d) * steQ w + z (Fin.last d) := by positivity
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact absurd h hpos.ne'
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hs
  · have := hc j
    rw [hs] at this
    exact mul_left_cancel₀ (hw.ne') this

end HRS.MS.Thm

end
