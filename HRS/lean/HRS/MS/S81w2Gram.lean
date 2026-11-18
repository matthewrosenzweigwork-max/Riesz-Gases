import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# S8.1 (worker S81W2): an abstract Gram identity for a bounded synthesis operator

`s81w2_gram`: if `S : ℓ² → H` and `B : H → H` are bounded and `⟨S e_k, B S e_l⟩ = c δ_{kl}` on the unit sequences,
then `⟨S x, B S y⟩ = c ⟨x, y⟩` for all `x, y ∈ ℓ²`.  (Used with `S` the bounded synthesis `Σ z_l e_l` of S8.8 A04 and
`B` the resolvent `(I+βK)⁻¹`, `c = β⁻¹`, to get the spectral form of the susceptibility covariance.)
-/

set_option autoImplicit false

noncomputable section
open Filter Topology

namespace HRS.Whole.S81W2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s81w2_gram_step1 (S : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] H) (B : H →L[ℝ] H) (c : ℝ)
    (hB : ∀ k l : ℕ, inner ℝ (S (lp.single 2 k (1 : ℝ))) (B (S (lp.single 2 l (1 : ℝ)))) =
      if k = l then c else 0) (k : ℕ) (y : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ (S (lp.single 2 k (1 : ℝ))) (B (S y)) = c * y k := by
  have hy : HasSum (fun l => lp.single 2 l (y l)) y := lp.hasSum_single (by simp) y
  have h1 := (hy.mapL ((innerSL ℝ (S (lp.single 2 k (1 : ℝ)))).comp (B.comp S)))
  have h2 : HasSum (fun l : ℕ => y l * (if k = l then c else 0)) (c * y k) := by
    have := hasSum_ite_eq k (c * y k)
    convert this using 1
    ext l
    by_cases h : k = l
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]
  refine (h1.unique ?_)
  convert h2 using 1
  ext l
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  have : lp.single (E := fun _ : ℕ => ℝ) 2 l (y l) = y l • lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ) := by
    rw [← lp.single_smul]; simp
  rw [this, map_smul, map_smul, inner_smul_right, hB]

theorem s81w2_gram (S : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] H) (B : H →L[ℝ] H) (c : ℝ)
    (hB : ∀ k l : ℕ, inner ℝ (S (lp.single 2 k (1 : ℝ))) (B (S (lp.single 2 l (1 : ℝ)))) =
      if k = l then c else 0) (x y : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ (S x) (B (S y)) = c * inner ℝ x y := by
  have hx : HasSum (fun k => lp.single 2 k (x k)) x := lp.hasSum_single (by simp) x
  have h1 := (hx.mapL ((innerSL ℝ).flip (B (S y)) |>.comp S))
  have h2 : HasSum (fun k : ℕ => c * (x k * y k)) (c * inner ℝ x y) := by
    have := (lp.hasSum_inner x y).mul_left c
    convert this using 1
    ext k
    simp [mul_comm]
  refine h1.unique ?_
  convert h2 using 1
  ext k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply]
  have : lp.single (E := fun _ : ℕ => ℝ) 2 k (x k) = x k • lp.single (E := fun _ : ℕ => ℝ) 2 k (1 : ℝ) := by
    rw [← lp.single_smul]; simp
  rw [this, map_smul, inner_smul_left, s81w2_gram_step1 S B c hB k y]
  simp [mul_comm, mul_left_comm]

end HRS.Whole.S81W2
