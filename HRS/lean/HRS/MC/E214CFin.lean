import HRS.MC.E214CPol
import HRS.MC.S7PICPoly

/-!
# E214C (part 2): 3-fold finite-rank algebra and the final lemma

`e214_tensor_zero_of_cubes`: a symmetric `D ∈ projTensor (PathSpace d m T) 3` killing all cubes is `0`.
-/

noncomputable section

open Filter Topology

namespace HRS.MC.E214C

open HRS HRS.Sec7 HRS.MC.E213U18

section Alg

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Re-indexing `Fin 3 → ι ≃ ι × ι × ι`. -/
def pi3Equiv (ι : Type*) : (Fin 3 → ι) ≃ ι × ι × ι where
  toFun r := (r 0, r 1, r 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem compCLM3_eq {ι : Type*} [Fintype ι] (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X) (v : ι → X)
    (hP : ∀ w, P w = ∑ a, l a w • v a) (M : X [×3]→L[ℝ] ℝ) :
    M.compContinuousLinearMap (fun _ => P) =
      ∑ a, ∑ b, ∑ c, M ![v a, v b, v c] • trilin ![l a, l b, l c] := by
  classical
  ext w
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hP,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.map_sum M (fun i (a : ι) => l a (w i) • v a)]
  have hr : ∑ a, ∑ b, ∑ c, M ![v a, v b, v c] * (l a (w 0) * l b (w 1) * l c (w 2)) =
      ∑ p : ι × ι × ι, M ![v p.1, v p.2.1, v p.2.2] * (l p.1 (w 0) * l p.2.1 (w 1) * l p.2.2 (w 2)) := by
    simp only [Fintype.sum_prod_type]
  have hl : ∀ a b c : ι, (trilin ![l a, l b, l c]) w = l a (w 0) * l b (w 1) * l c (w 2) := by
    intro a b c; rw [trilin_apply]; rfl
  simp only [hl]
  rw [hr]
  refine Fintype.sum_equiv (pi3Equiv ι) _ _ (fun r => ?_)
  show M (fun i => l (r i) (w i) • v (r i)) = _
  rw [M.map_smul_univ]
  have e : (fun i => v (r i)) = ![v (r 0), v (r 1), v (r 2)] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  show _ = M ![v (r 0), v (r 1), v (r 2)] * (l (r 0) (w 0) * l (r 1) (w 1) * l (r 2) (w 2))
  simp only [Fin.prod_univ_three, smul_eq_mul]
  ring

theorem tensorPow3_eq_zero {ι : Type*} [Fintype ι] (P : X →L[ℝ] X) (l : ι → StrongDual ℝ X)
    (v : ι → X) (hP : ∀ w, P w = ∑ a, l a w • v a) (D : TensorDual X 3)
    (h : ∀ a b c, D (trilin ![l a, l b, l c]) = 0) : tensorPow 3 P D = 0 := by
  ext M
  have e : tensorPow 3 P D M = D (M.compContinuousLinearMap (fun _ => P)) := rfl
  rw [e, compCLM3_eq P l v hP M]
  simp only [map_sum, map_smul, h, smul_zero, Finset.sum_const_zero]
  rfl

end Alg

variable {d : ℕ}

/-- **Final lemma.** A symmetric element of `projTensor (PathSpace d m T) 3` which kills all cubes `L⊗L⊗L`
of continuous linear functionals is zero. -/
theorem e214_tensor_zero_of_cubes (d : ℕ) (m T : ℝ) (hT : 0 < T)
    (D : TensorDual (PathSpace d m T) 3) (hD : D ∈ projTensor (PathSpace d m T) 3)
    (hsym : ∀ (M : (PathSpace d m T) [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)),
      D (M.domDomCongr σ) = D M)
    (hcube : ∀ L : StrongDual ℝ (PathSpace d m T), D (trilin ![L, L, L]) = 0) : D = 0 := by
  obtain ⟨Pj, hPj, -, -, hconv⟩ := projection_strong_proof (d := d) m T hT
  have hprod := e214_prod_zero_of_cubes D hsym hcube
  have hzero : ∀ L, tensorPow 3 (Pj L) D = 0 := by
    intro L
    refine tensorPow3_eq_zero (Pj L)
      (fun a : Fin (2 ^ L + 1) × ↥(HRS.MC.Sec7.S7PIC.S7PIC_box d L) =>
        HRS.MC.Sec7.S7PIC.S7PIC_lf m T (HRS.MC.Sec7.S7PIC.S7PIC_node T hT.le L a.1) a.2)
      (fun a => HRS.MC.Sec7.S7PIC.S7PIC_vpath m T L a.1 a.2) (fun w => ?_) D
      (fun a b c => hprod _ _ _)
    rw [hPj, HRS.MC.Sec7.S7PIC.S7PIC_projPoly_eq_sum]
  have h1 := hconv 3 D hD
  have h2 : Tendsto (fun L => tensorPow 3 (Pj L) D) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end HRS.MC.E214C
