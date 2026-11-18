import HRS.MC.S7PICPoly

/-!
# Cubic tensor uniqueness, part 1: the `j`-fold finite-rank algebra

If `P w = ∑_a l_a(w) • v_a`, then `P^{⊗j} K` depends only on the values of `K` on the product forms
`l_{r 0} ⊗ ⋯ ⊗ l_{r (j-1)}`.  (Generalisation of `S7PIC_compCLM_eq`, `S7PIC_tensorPow_eq`, `S7PIC_eq_of_proj`.)
-/

noncomputable section

open Filter Topology

namespace HRS.MC.CUB

open HRS HRS.Sec7

set_option maxSynthPendingDepth 3

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The product tensor `l₀ ⊗ ⋯ ⊗ l_{j-1}` as a bounded `j`-linear form on `X`. -/
abbrev prodFormN (j : ℕ) (l : Fin j → StrongDual ℝ X) : X [×j]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ j ℝ).compContinuousLinearMap l

theorem compCLM_eq {ι : Type*} [Fintype ι] (j : ℕ) (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X) (v : ι → X)
    (hP : ∀ w, P w = ∑ a, l a w • v a) (M : X [×j]→L[ℝ] ℝ) :
    M.compContinuousLinearMap (fun _ => P) =
      ∑ r : Fin j → ι, M (fun i => v (r i)) • prodFormN j (fun i => l (r i)) := by
  classical
  ext w
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hP,
    sum_apply, smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.map_sum M (fun i (a : ι) => l a (w i) • v a)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [M.map_smul_univ]
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn,
    smul_eq_mul]
  rw [mul_comm]

theorem tensorPow_eq_of_agree {ι : Type*} [Fintype ι] (j : ℕ) (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X)
    (v : ι → X) (hP : ∀ w, P w = ∑ a, l a w • v a) (K₁ K₂ : TensorDual X j)
    (h : ∀ r : Fin j → ι, K₁ (prodFormN j (fun i => l (r i))) = K₂ (prodFormN j (fun i => l (r i)))) :
    tensorPow j P K₁ = tensorPow j P K₂ := by
  ext M
  have e : ∀ J : TensorDual X j, tensorPow j P J M = J (M.compContinuousLinearMap (fun _ => P)) :=
    fun J => rfl
  rw [e, e, compCLM_eq j P l v hP M]
  simp only [map_sum, map_smul, h]

theorem eq_of_proj {j : ℕ} (Pj : ℕ → (X →L[ℝ] X)) (K₁ K₂ : TensorDual X j)
    (h₁ : Tendsto (fun L => tensorPow j (Pj L) K₁) atTop (𝓝 K₁))
    (h₂ : Tendsto (fun L => tensorPow j (Pj L) K₂) atTop (𝓝 K₂))
    (h : ∀ L, tensorPow j (Pj L) K₁ = tensorPow j (Pj L) K₂) : K₁ = K₂ := by
  have : Tendsto (fun L => tensorPow j (Pj L) K₁) atTop (𝓝 K₂) := by
    simpa [h] using h₂
  exact tendsto_nhds_unique h₁ this

end HRS.MC.CUB
