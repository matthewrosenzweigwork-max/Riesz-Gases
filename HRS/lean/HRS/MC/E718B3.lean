import HRS.MC.E718B2

/-!
# Row 7.18 (packet e718b), file 3: Hilbert-Schmidt bookkeeping for a Hilbert basis

`Pb b L` is the orthogonal projection onto `span (b_0, …, b_{L-1})`, `Tb A b L = A - P A P`.  Everything is
done with the coefficients `⟪b_i, A b_j⟫` (Parseval), and Bessel's inequality for a finite orthonormal family.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E718B

section HS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma hasSum_sq (b : HilbertBasis ℕ ℝ H) (x : H) :
    HasSum (fun i => (inner ℝ (b i) x) ^ 2) (‖x‖ ^ 2) := by
  have := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at this
  convert this using 1
  ext i
  rw [real_inner_comm (b i) x]
  ring

/-- Orthogonal projection onto `span (b_0, …, b_{L-1})`. -/
def Pb (b : HilbertBasis ℕ ℝ H) (L : ℕ) : H →L[ℝ] H :=
  ∑ i ∈ Finset.range L, (innerSL ℝ (b i)).smulRight (b i)

variable (b : HilbertBasis ℕ ℝ H) (L : ℕ)

lemma Pb_apply (x : H) : Pb b L x = ∑ i ∈ Finset.range L, inner ℝ (b i) x • b i := by
  simp [Pb]

lemma inner_Pb (x y : H) :
    inner ℝ x (Pb b L y) = ∑ i ∈ Finset.range L, inner ℝ (b i) x * inner ℝ (b i) y := by
  rw [Pb_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_comm x (b i)]
  ring

lemma Pb_selfadj (x y : H) : inner ℝ (Pb b L x) y = inner ℝ x (Pb b L y) := by
  rw [real_inner_comm, inner_Pb, inner_Pb]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma inner_b_Pb (i : ℕ) (y : H) :
    inner ℝ (b i) (Pb b L y) = if i < L then inner ℝ (b i) y else 0 := by
  rw [inner_Pb]
  have : ∀ i' : ℕ, inner ℝ (b i') (b i) = if i' = i then (1 : ℝ) else 0 :=
    fun i' => orthonormal_iff_ite.1 b.orthonormal i' i
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]

lemma Pb_b (j : ℕ) : Pb b L (b j) = if j < L then b j else 0 := by
  rw [Pb_apply]
  have : ∀ i' : ℕ, inner ℝ (b i') (b j) = if i' = j then (1 : ℝ) else 0 :=
    fun i' => orthonormal_iff_ite.1 b.orthonormal i' j
  simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_range]

/-- `A - P A P`. -/
def Tb (A : H →L[ℝ] H) : H →L[ℝ] H := A - ((Pb b L).comp A).comp (Pb b L)

lemma Tb_apply (A : H →L[ℝ] H) (x : H) : Tb b L A x = A x - Pb b L (A (Pb b L x)) := rfl

lemma inner_Tb (A : H →L[ℝ] H) (i j : ℕ) :
    inner ℝ (b i) (Tb b L A (b j)) = if i < L ∧ j < L then 0 else inner ℝ (b i) (A (b j)) := by
  rw [Tb_apply, inner_sub_right, inner_b_Pb, Pb_b]
  by_cases hi : i < L <;> by_cases hj : j < L <;> simp [hi, hj]

lemma Tb_symm (A : H →L[ℝ] H) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (x y : H) :
    inner ℝ (Tb b L A x) y = inner ℝ x (Tb b L A y) := by
  rw [Tb_apply, Tb_apply, inner_sub_left, inner_sub_right, Pb_selfadj, hA, ← Pb_selfadj b L x (A (Pb b L y))]
  rw [hA]

lemma Tb_sq_le (A : H →L[ℝ] H) (j : ℕ) : ‖Tb b L A (b j)‖ ^ 2 ≤ ‖A (b j)‖ ^ 2 := by
  rw [← (hasSum_sq b (Tb b L A (b j))).tsum_eq, ← (hasSum_sq b (A (b j))).tsum_eq]
  refine (hasSum_sq b (Tb b L A (b j))).summable.tsum_le_tsum (fun i => ?_)
    (hasSum_sq b (A (b j))).summable
  rw [inner_Tb]
  split_ifs <;> simp [sq_nonneg]

lemma Tb_sq_eq (A : H →L[ℝ] H) (j : ℕ) :
    ‖Tb b L A (b j)‖ ^ 2 =
      ∑' i, (if i < L ∧ j < L then 0 else (inner ℝ (b i) (A (b j))) ^ 2) := by
  rw [← (hasSum_sq b (Tb b L A (b j))).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [inner_Tb]
  split_ifs <;> simp

/-- The tail `∑_j ‖(A - P_L A P_L) b_j‖²` tends to `0` for a Hilbert-Schmidt `A`. -/
lemma Tb_tail (A : H →L[ℝ] H) (hHS : Summable fun j => ‖A (b j)‖ ^ 2) :
    Tendsto (fun L => ∑' j, ‖Tb b L A (b j)‖ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun L j => ‖Tb b L A (b j)‖ ^ 2) (g := fun _ => (0 : ℝ))
    (bound := fun j => ‖A (b j)‖ ^ 2) hHS ?_ ?_
  · simpa using h
  · intro j
    simp_rw [Tb_sq_eq]
    have h2 := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
      (f := fun L i => (if i < L ∧ j < L then 0 else (inner ℝ (b i) (A (b j))) ^ 2 : ℝ))
      (g := fun _ => (0 : ℝ)) (bound := fun i => (inner ℝ (b i) (A (b j))) ^ 2)
      (hasSum_sq b (A (b j))).summable ?_ ?_
    · simpa using h2
    · intro i
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop i, eventually_gt_atTop j] with L hi hj
      simp [hi, hj]
    · refine Eventually.of_forall fun L i => ?_
      split_ifs <;> simp [sq_nonneg]
  · refine Eventually.of_forall fun L j => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Tb_sq_le b L A j

/-- Bessel-type bound: the Hilbert-Schmidt sum of a symmetric `T` over a finite orthonormal family
is at most its sum over a Hilbert basis. -/
lemma sum_sq_le (T : H →L[ℝ] H) (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hs : Summable fun j => ‖T (b j)‖ ^ 2) {m : ℕ} (f : Fin m → H) (hf : Orthonormal ℝ f) :
    ∑ l, ‖T (f l)‖ ^ 2 ≤ ∑' j, ‖T (b j)‖ ^ 2 := by
  have e : ∀ l, ‖T (f l)‖ ^ 2 = ∑' j, (inner ℝ (T (b j)) (f l)) ^ 2 := by
    intro l
    rw [← (hasSum_sq b (T (f l))).tsum_eq]
    refine tsum_congr fun j => ?_
    rw [hT]
  have hsl : ∀ l, Summable fun j => (inner ℝ (T (b j)) (f l)) ^ 2 := by
    intro l
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hs
    have h1 := abs_real_inner_le_norm (T (b j)) (f l)
    rw [hf.1 l] at h1
    have h2 : (inner ℝ (T (b j)) (f l)) ^ 2 ≤ (‖T (b j)‖ * 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    simpa using h2
  simp_rw [e]
  rw [← Summable.tsum_finsetSum (fun l _ => hsl l)]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun l _ => hsl l) hs
  have := hf.sum_inner_products_le (s := Finset.univ) (x := T (b j))
  simpa [Real.norm_eq_abs, sq_abs, real_inner_comm] using this

/-- Hilbert-Schmidt summability is independent of the Hilbert basis. -/
lemma summable_other_basis (A : H →L[ℝ] H) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (b b' : HilbertBasis ℕ ℝ H) (hHS : Summable fun j => ‖A (b j)‖ ^ 2) :
    Summable fun j => ‖A (b' j)‖ ^ 2 := by
  refine summable_of_sum_range_le (c := ∑' j, ‖A (b j)‖ ^ 2) (fun n => sq_nonneg _) fun n => ?_
  have hon : Orthonormal ℝ (fun l : Fin n => b' (l : ℕ)) :=
    b'.orthonormal.comp _ Fin.val_injective
  have := sum_sq_le b A hA hHS (fun l : Fin n => b' (l : ℕ)) hon
  rwa [Finset.sum_range]

/-- The coefficients of the compression `P A P` in terms of the matrix `⟪b_i, A b_j⟫`. -/
lemma sec_coeff (A : H →L[ℝ] H) (x y : H) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      inner ℝ (b i) (A (b j)) * inner ℝ x (b i) * inner ℝ y (b j) =
      inner ℝ x (Pb b L (A (Pb b L y))) := by
  rw [inner_Pb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pb_apply, map_sum, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, real_inner_smul_right, real_inner_comm x (b i), real_inner_comm y (b j)]
  ring

end HS

end HRS.MC.E718B
