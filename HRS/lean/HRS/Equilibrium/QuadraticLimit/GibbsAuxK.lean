import Mathlib

/-!
# Lemma 7.5, `q08_gibbs_approx`: dimension-free matrix estimates (prefix `q08gl_`)
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace HRS.Q08

section MatrixNorms

variable {m : ℕ}

/-- Squared Euclidean norm of a vector. -/
def q08gl_nsq (v : Fin m → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Squared Frobenius norm. -/
def q08gl_F2 (X : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2

theorem q08gl_nsq_nonneg (v : Fin m → ℝ) : 0 ≤ q08gl_nsq v := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem q08gl_F2_nonneg (X : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ q08gl_F2 X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem q08gl_F2_transpose (X : Matrix (Fin m) (Fin m) ℝ) : q08gl_F2 Xᵀ = q08gl_F2 X := by
  unfold q08gl_F2
  rw [Finset.sum_comm]
  rfl

theorem q08gl_F2_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℝ) : q08gl_F2 (c • X) = c ^ 2 * q08gl_F2 X := by
  unfold q08gl_F2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_pow]

theorem q08gl_F2_neg (X : Matrix (Fin m) (Fin m) ℝ) : q08gl_F2 (-X) = q08gl_F2 X := by
  have := q08gl_F2_smul (-1) X
  simpa using this

theorem q08gl_contr_F2 (Y : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    q08gl_nsq (Y *ᵥ v) ≤ q08gl_F2 Y * q08gl_nsq v := by
  unfold q08gl_nsq q08gl_F2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Y i j) v
  simpa [Matrix.mulVec, dotProduct] using this

theorem q08gl_F2_mul_left (Y X : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hY : ∀ v, q08gl_nsq (Y *ᵥ v) ≤ c * q08gl_nsq v) : q08gl_F2 (Y * X) ≤ c * q08gl_F2 X := by
  have h1 : q08gl_F2 (Y * X) = ∑ j, ∑ i, (Y * X) i j ^ 2 := by
    unfold q08gl_F2; exact Finset.sum_comm
  have h2 : q08gl_F2 X = ∑ j, ∑ i, X i j ^ 2 := by
    unfold q08gl_F2; exact Finset.sum_comm
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := hY (fun k => X k j)
  simpa [q08gl_nsq, Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

theorem q08gl_F2_mul_right (X Y : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hY : ∀ v, q08gl_nsq (Yᵀ *ᵥ v) ≤ c * q08gl_nsq v) : q08gl_F2 (X * Y) ≤ c * q08gl_F2 X := by
  have := q08gl_F2_mul_left Yᵀ Xᵀ c hY
  rw [← Matrix.transpose_mul, q08gl_F2_transpose, q08gl_F2_transpose] at this
  exact this

/-- For `0 ≤ Σ ≤ 1`: `|Σ x|² ≤ ⟨x, Σ x⟩`. -/
theorem q08gl_psd_firm (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ = S) (h0 : ∀ x, 0 ≤ x ⬝ᵥ S *ᵥ x)
    (h1 : ∀ x, x ⬝ᵥ S *ᵥ x ≤ q08gl_nsq x) (x : Fin m → ℝ) :
    q08gl_nsq (S *ᵥ x) ≤ x ⬝ᵥ S *ᵥ x := by
  set y := S *ᵥ x with hy
  have hsym : ∀ a b : Fin m → ℝ, a ⬝ᵥ S *ᵥ b = b ⬝ᵥ S *ᵥ a := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]
  have hq : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ S *ᵥ y) * (t * t) + (2 * (x ⬝ᵥ S *ᵥ y)) * t + x ⬝ᵥ S *ᵥ x := by
    intro t
    have := h0 (x + t • y)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      hsym y x] at this
    nlinarith [this]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hyy : q08gl_nsq y = x ⬝ᵥ S *ᵥ y := by
    unfold q08gl_nsq
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
    simp [dotProduct, hy, sq]
  have hq1 := h1 y
  have hn0 := q08gl_nsq_nonneg y
  have hx0 := h0 x
  rw [← hyy] at hd
  by_contra hcon
  push Not at hcon
  have h2 : q08gl_nsq y * q08gl_nsq y ≤ (x ⬝ᵥ S *ᵥ x) * q08gl_nsq y := by nlinarith
  by_cases hz : q08gl_nsq y = 0
  · rw [hz] at hcon; linarith
  · have hp : 0 < q08gl_nsq y := lt_of_le_of_ne hn0 (Ne.symm hz)
    nlinarith

theorem q08gl_nsq_add_le (a b : Fin m → ℝ) : q08gl_nsq (a + b) ≤ 2 * q08gl_nsq a + 2 * q08gl_nsq b := by
  unfold q08gl_nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a i - b i)]

/-- Inversion of an approximate resolvent: if `(1 + β K^U) Σ = 1 + E` with `E` small in Frobenius norm,
then `Σ` is invertible and `K' = β⁻¹ (Σ⁻¹ - 1)` is a positive semidefinite matrix with
`Σ (1 + β K') = 1` which is Frobenius-close to `K^U`. -/
theorem q08gl_matrix_inv (β : ℝ) (hβ : 0 < β) (KU S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ = S)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ S *ᵥ x) (h1 : ∀ x, x ⬝ᵥ S *ᵥ x ≤ q08gl_nsq x)
    (Fk e : ℝ) (hFk : q08gl_F2 KU ≤ Fk ^ 2) (he0 : 0 ≤ e) (he : e ≤ 1 / 2)
    (hE : q08gl_F2 ((1 + β • KU) * S - 1) ≤ e ^ 2) :
    ∃ K' : Matrix (Fin m) (Fin m) ℝ, K'ᵀ = K' ∧ K'.PosSemidef ∧ S * (1 + β • K') = 1 ∧
      q08gl_F2 (K' - KU) ≤ 8 * (1 + β ^ 2 * Fk ^ 2) * e ^ 2 / β ^ 2 := by
  set E : Matrix (Fin m) (Fin m) ℝ := (1 + β • KU) * S - 1 with hEdef
  have hEv : ∀ v, q08gl_nsq (E *ᵥ v) ≤ e ^ 2 * q08gl_nsq v := fun v =>
    (q08gl_contr_F2 E v).trans (mul_le_mul_of_nonneg_right hE (q08gl_nsq_nonneg v))
  have hKv : ∀ v, q08gl_nsq (KU *ᵥ v) ≤ Fk ^ 2 * q08gl_nsq v := fun v =>
    (q08gl_contr_F2 KU v).trans (mul_le_mul_of_nonneg_right hFk (q08gl_nsq_nonneg v))
  have he2 : e ^ 2 ≤ 1 / 4 := by nlinarith
  -- key identity: `(1 + β K) S z = z + E z`
  have hkey : ∀ z, (1 + β • KU) *ᵥ (S *ᵥ z) = z + E *ᵥ z := fun z => by
    rw [Matrix.mulVec_mulVec, hEdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  -- bound of the inverse
  have hinv : ∀ z, q08gl_nsq z ≤ 4 * q08gl_nsq ((1 + β • KU) *ᵥ (S *ᵥ z)) := fun z => by
    have h2 : z = ((1 + β • KU) *ᵥ (S *ᵥ z)) + (-(E *ᵥ z)) := by rw [hkey]; abel
    have h3 := q08gl_nsq_add_le ((1 + β • KU) *ᵥ (S *ᵥ z)) (-(E *ᵥ z))
    rw [← h2] at h3
    have h4 : q08gl_nsq (-(E *ᵥ z)) = q08gl_nsq (E *ᵥ z) := by simp [q08gl_nsq]
    rw [h4] at h3
    have := hEv z
    nlinarith [q08gl_nsq_nonneg z]
  -- injectivity of `S`
  have hinj : Function.Injective S.mulVec := by
    intro a b hab
    have hz : S *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hab
    suffices a - b = 0 from sub_eq_zero.1 this
    generalize a - b = z at hz
    have := hinv z
    have h5 : (1 + β • KU) *ᵥ (S *ᵥ z) = 0 := by rw [show S *ᵥ z = 0 from hz]; simp
    rw [h5] at this
    have h6 : q08gl_nsq (0 : Fin m → ℝ) = 0 := by simp [q08gl_nsq]
    rw [h6] at this
    have h7 : q08gl_nsq z = 0 := le_antisymm (by linarith) (q08gl_nsq_nonneg z)
    funext i
    have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i)) |>.1 h7 i (Finset.mem_univ i)
    simpa using this
  have hunit : IsUnit S := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hunit
  set Si : Matrix (Fin m) (Fin m) ℝ := S⁻¹ with hSi
  have hSSi : S * Si = 1 := Matrix.mul_nonsing_inv S hdet
  have hSiS : Si * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hSit : Siᵀ = Si := by rw [hSi, Matrix.transpose_nonsing_inv, hS]
  set K' : Matrix (Fin m) (Fin m) ℝ := β⁻¹ • (Si - 1) with hK'
  have hKt : K'ᵀ = K' := by
    rw [hK', Matrix.transpose_smul, Matrix.transpose_sub, hSit, Matrix.transpose_one]
  have hSK : S * (1 + β • K') = 1 := by
    have : 1 + β • K' = Si := by
      rw [hK', smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]; abel
    rw [this, hSSi]
  refine ⟨K', hKt, ?_, hSK, ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hKt) fun x => ?_
    simp only [star_trivial]
    have hw := q08gl_psd_firm S hS h0 h1 (Si *ᵥ x)
    have hx : S *ᵥ (Si *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hSSi, Matrix.one_mulVec]
    rw [hx] at hw
    have e1 : x ⬝ᵥ K' *ᵥ x = β⁻¹ * (x ⬝ᵥ Si *ᵥ x - q08gl_nsq x) := by
      rw [hK', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec,
        dotProduct_sub]
      simp [q08gl_nsq, dotProduct, sq]
    have e2 : x ⬝ᵥ Si *ᵥ x = (Si *ᵥ x) ⬝ᵥ x := dotProduct_comm _ _
    rw [e1, e2]
    exact mul_nonneg (inv_nonneg.2 hβ.le) (by linarith)
  · have hSiv : ∀ y, q08gl_nsq (Si *ᵥ y) ≤ 8 * (1 + β ^ 2 * Fk ^ 2) * q08gl_nsq y := by
      intro y
      have h1' := hinv (Si *ᵥ y)
      have hy : S *ᵥ (Si *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hSSi, Matrix.one_mulVec]
      rw [hy] at h1'
      have h2' : q08gl_nsq ((1 + β • KU) *ᵥ y) ≤ 2 * q08gl_nsq y + 2 * (β ^ 2 * (Fk ^ 2 * q08gl_nsq y)) := by
        have h3 : (1 + β • KU) *ᵥ y = y + β • (KU *ᵥ y) := by
          rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
        rw [h3]
        refine (q08gl_nsq_add_le _ _).trans ?_
        have h4 : q08gl_nsq (β • (KU *ᵥ y)) = β ^ 2 * q08gl_nsq (KU *ᵥ y) := by
          simp only [q08gl_nsq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        rw [h4]
        have := hKv y
        nlinarith [sq_nonneg β]
      nlinarith [q08gl_nsq_nonneg y]
    have hX : K' - KU = β⁻¹ • (-(E * Si)) := by
      have hES : E * Si = (1 + β • KU) - Si := by
        rw [hEdef, sub_mul, mul_assoc, hSSi, mul_one, Matrix.one_mul]
      rw [hES, hK']
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    rw [hX, q08gl_F2_smul, q08gl_F2_neg]
    have h1' : q08gl_F2 (E * Si) ≤ 8 * (1 + β ^ 2 * Fk ^ 2) * q08gl_F2 E :=
      q08gl_F2_mul_right E Si _ (fun v => by rw [hSit]; exact hSiv v)
    have h2' : q08gl_F2 E ≤ e ^ 2 := hE
    have hg : 0 ≤ 8 * (1 + β ^ 2 * Fk ^ 2) := by positivity
    calc β⁻¹ ^ 2 * q08gl_F2 (E * Si) ≤ β⁻¹ ^ 2 * (8 * (1 + β ^ 2 * Fk ^ 2) * e ^ 2) :=
          mul_le_mul_of_nonneg_left (h1'.trans (mul_le_mul_of_nonneg_left h2' hg)) (sq_nonneg _)
      _ = 8 * (1 + β ^ 2 * Fk ^ 2) * e ^ 2 / β ^ 2 := by field_simp

end MatrixNorms

end HRS.Q08

end
