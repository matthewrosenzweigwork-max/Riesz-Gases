import HRS.MS.Fp81S21EmbedField8

/-! Finite coordinate projections on the common Hilbert coefficient space. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open scoped RealInnerProductSpace
open Filter Topology

/-- The canonical coordinate Hilbert basis of the coefficient space. -/
def fp81s21_coeffBasis : HilbertBasis ℕ ℝ r26t6_Coeff := default

/-- Projection onto the first `m` coordinates, written as a finite sum of
orthogonal rank-one maps. -/
def fp81s21_projectField (m : ℕ) : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
  ∑ j ∈ Finset.range m,
    (innerSL ℝ (fp81s21_coeffBasis j)).smulRight (fp81s21_coeffBasis j)

theorem fp81s21_projectField_apply (m : ℕ) (z : r26t6_Coeff) :
    fp81s21_projectField m z =
      ∑ j ∈ Finset.range m,
        inner ℝ (fp81s21_coeffBasis j) z • fp81s21_coeffBasis j := by
  simp [fp81s21_projectField, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem fp81s21_projectField_tendsto (z : r26t6_Coeff) :
    Tendsto (fun m => fp81s21_projectField m z) atTop (𝓝 z) := by
  have hs : HasSum
      (fun j : ℕ => inner ℝ (fp81s21_coeffBasis j) z • fp81s21_coeffBasis j) z := by
    simpa [HilbertBasis.repr_apply_apply] using
      (fp81s21_coeffBasis.hasSum_repr z)
  have ht := hs.tendsto_sum_nat
  simpa [fp81s21_projectField_apply] using ht

theorem fp81s21_projectField_adjoint (m : ℕ) :
    (fp81s21_projectField m).adjoint = fp81s21_projectField m := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℝ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [fp81s21_projectField_apply, fp81s21_projectField_apply]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm x (fp81s21_coeffBasis j)]
  simp
  ring

theorem fp81s21_projectField_norm_le (m : ℕ) (z : r26t6_Coeff) :
    ‖fp81s21_projectField m z‖ ≤ ‖z‖ := by
  have he : ∀ i j : ℕ,
      inner ℝ (fp81s21_coeffBasis i) (fp81s21_coeffBasis j) =
        if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 fp81s21_coeffBasis.orthonormal
  have hsq : ‖fp81s21_projectField m z‖ ^ 2 =
      ∑ j ∈ Finset.range m,
        (inner ℝ (fp81s21_coeffBasis j) z) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, fp81s21_projectField_apply]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      he, conj_trivial]
    simp only [Finset.sum_ite_eq', sq]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have hb := fp81s21_coeffBasis.orthonormal.sum_inner_products_le z
    (s := Finset.range m)
  have hle :
      (∑ j ∈ Finset.range m,
        (inner ℝ (fp81s21_coeffBasis j) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    simpa [Real.norm_eq_abs, real_inner_comm, sq_abs] using hb
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  calc
    ‖fp81s21_projectField m z‖ ^ 2 =
        ∑ j ∈ Finset.range m,
          (inner ℝ (fp81s21_coeffBasis j) z) ^ 2 := hsq
    _ ≤ ‖z‖ ^ 2 := hle

theorem fp81s21_projectField_isCompactOperator (m : ℕ) :
    IsCompactOperator (fp81s21_projectField m) := by
  classical
  let W : Submodule ℝ r26t6_Coeff :=
    Submodule.span ℝ
      ((fun j : ℕ => fp81s21_coeffBasis j) ''
        (Finset.range m : Set ℕ))
  have hfinite :
      ((fun j : ℕ => fp81s21_coeffBasis j) ''
        (Finset.range m : Set ℕ)).Finite :=
    (Finset.finite_toSet (Finset.range m)).image
      (fun j : ℕ => fp81s21_coeffBasis j)
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.span_of_finite ℝ hfinite
  have hmem : ∀ z, fp81s21_projectField m z ∈ W := by
    intro z
    rw [fp81s21_projectField_apply]
    refine Submodule.sum_mem _ fun j hj => ?_
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, hj, rfl⟩)
  let T : r26t6_Coeff →L[ℝ] W :=
    (fp81s21_projectField m).codRestrict W hmem
  have hid : IsCompactOperator (id : W → W) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).2 inferInstance
  have hc : IsCompactOperator ((id : W → W) ∘ T) := hid.comp_clm T
  exact hc.clm_comp W.subtypeL

#print axioms HRS.Fp81.S21.fp81s21_projectField_tendsto
#print axioms HRS.Fp81.S21.fp81s21_projectField_adjoint
#print axioms HRS.Fp81.S21.fp81s21_projectField_norm_le
#print axioms HRS.Fp81.S21.fp81s21_projectField_isCompactOperator

end HRS.Fp81.S21
