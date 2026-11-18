import HRS.MS.SpecAux7

/-!
# S8P: the finite-section inequality for the PSD-root lemma of S8.7

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  With `V_{ij} = x_{ij}/(e_i+e_j)` and `S ≥ 0`:
`∑_{i,j∈F} V_{ij} ⟨ξ_i, ξ_j⟩ ≥ -(1/2) ∑_{i∈F} ‖ξ_i‖²` for every finite `F`
(`s8p_finite_ineq`; step 3-4 of the proof in `docs/S8_PLAN.md` section 2.4).
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*}

theorem s8p_pointwise [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hS : ∀ x, 0 ≤ ⟪S x, x⟫) (e : ι → ℝ) (he : ∀ i, 0 < e i) (b : HilbertBasis ι ℝ H)
    (F : Finset ι) (w : ι → ℝ) :
    -(1 / 2) * ∑ i ∈ F, w i ^ 2 ≤
      ∑ i ∈ F, ∑ j ∈ F, (s8p_x S e b i j / (e i + e j)) * w i * w j := by
  have h0 := s8p_cauchy_psd S hSs hS b e he F w
  have hsplit : ∀ i j, ⟪b i, S (b j)⟫ * w i * w j / (e i + e j) =
      (s8p_x S e b i j / (e i + e j)) * w i * w j +
        (if i = j then e j else 0) * w i * w j / (e i + e j) := by
    intro i j
    rw [s8p_x_eq]; ring
  simp_rw [hsplit, Finset.sum_add_distrib] at h0
  have hdiag : ∑ i ∈ F, ∑ j ∈ F, (if i = j then e j else 0) * w i * w j / (e i + e j) =
      (1 / 2) * ∑ i ∈ F, w i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi]
    · have hei : e i ≠ 0 := (he i).ne'
      simp
      field_simp
      ring
    · intro j _ hji
      simp [Ne.symm hji]
  rw [hdiag] at h0
  linarith

theorem s8p_finite_ineq [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hS : ∀ x, 0 ≤ ⟪S x, x⟫) (e : ι → ℝ) (he : ∀ i, 0 < e i) (b : HilbertBasis ι ℝ H)
    (F : Finset ι) :
    -(1 / 2) * ∑ i ∈ F, ‖s8p_xi S e b i‖ ^ 2 ≤
      ∑ i ∈ F, ∑ j ∈ F, (s8p_x S e b i j / (e i + e j)) * ⟪s8p_xi S e b i, s8p_xi S e b j⟫ := by
  have hL : HasSum (fun k => -(1 / 2) * ∑ i ∈ F, s8p_x S e b k i ^ 2)
      (-(1 / 2) * ∑ i ∈ F, ‖s8p_xi S e b i‖ ^ 2) := by
    have := hasSum_sum (s := F) (f := fun i k => s8p_x S e b k i ^ 2)
      (a := fun i => ‖s8p_xi S e b i‖ ^ 2) fun i _ => s8p_x_col S e b i
    exact this.mul_left _
  have hR : HasSum (fun k => ∑ i ∈ F, ∑ j ∈ F,
      (s8p_x S e b i j / (e i + e j)) * s8p_x S e b k i * s8p_x S e b k j)
      (∑ i ∈ F, ∑ j ∈ F, (s8p_x S e b i j / (e i + e j)) * ⟪s8p_xi S e b i, s8p_xi S e b j⟫) := by
    refine hasSum_sum fun i _ => ?_
    refine hasSum_sum fun j _ => ?_
    have := (s8p_x_inner S e b i j).mul_left (s8p_x S e b i j / (e i + e j))
    convert this using 1
    funext k; ring
  refine hasSum_le (fun k => ?_) hL hR
  have := s8p_pointwise S hSs hS e he b F (fun i => s8p_x S e b k i)
  exact this

end HRS.MS.Spec
