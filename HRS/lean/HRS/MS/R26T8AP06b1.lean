import HRS.MS.R26T8AP21c

/-!
# S8.2 local Newton layer, packet T8A.P06b (part 1): one step of the joint-jet recursion
`dY Phi (Y,w) = D Phi (Y,w) o inl` (the `Y`-partial derivative, `dw` of `R26T8AMix` is the `w`-partial one).  For `Psi` of class `C^(j+1)`:
`|D^(j+1) Psi x| <= |D^j (dY Psi) x| + |D^j (dw Psi) x|`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section PartialY

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `Y`-partial derivative of a two-variable function. -/
def r26t8a_dY {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : E × E → V) (Yw : E × E) : E →L[ℝ] V :=
  (fderiv ℝ Φ Yw).comp (ContinuousLinearMap.inl ℝ E E)

theorem r26t8a_p06b_dY_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × E → V} {n : ℕ}
    (hΦ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ) : ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_dY Φ) :=
  (hΦ.fderiv_right (by push_cast; exact le_rfl)).clm_comp contDiff_const

/-- `precomposition with fst / snd`. -/
def r26t8a_pre (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E × E →L[ℝ] E) :
    (E →L[ℝ] V) →L[ℝ] (E × E →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ (E × E) E V).flip L

theorem r26t8a_pre_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E × E →L[ℝ] E)
    (a : E →L[ℝ] V) : r26t8a_pre V L a = a.comp L := rfl

theorem r26t8a_pre_norm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E × E →L[ℝ] E)
    (hL : ‖L‖ ≤ 1) : ‖r26t8a_pre V L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun a => ?_)
  rw [r26t8a_pre_apply, one_mul]
  exact (a.opNorm_comp_le L).trans (mul_le_of_le_one_right (norm_nonneg _) hL)

theorem r26t8a_joint_step {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) {Ψ : E × E → V}
    (hΨ : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) Ψ) (x : E × E) :
    ‖iteratedFDeriv ℝ (j + 1) Ψ x‖ ≤
      ‖iteratedFDeriv ℝ j (r26t8a_dY Ψ) x‖ + ‖iteratedFDeriv ℝ j (r26t8a_dw Ψ) x‖ := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have e : fderiv ℝ Ψ = fun y => r26t8a_pre V (ContinuousLinearMap.fst ℝ E E) (r26t8a_dY Ψ y) +
      r26t8a_pre V (ContinuousLinearMap.snd ℝ E E) (r26t8a_dw Ψ y) := by
    funext y
    rw [r26t8a_dw_eq hd, r26t8a_pre_apply, r26t8a_pre_apply]
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    simp only [r26t8a_dY, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    rw [← map_add]
    simp
  rw [← norm_iteratedFDeriv_fderiv, e]
  have h1 : ContDiffAt ℝ (j : WithTop ℕ∞) (r26t8a_dY Ψ) x := (r26t8a_p06b_dY_contDiff hΨ).contDiffAt
  have h2 : ContDiffAt ℝ (j : WithTop ℕ∞) (r26t8a_dw Ψ) x := (r26t8a_dw_contDiff hΨ).contDiffAt
  have hf1 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun y => r26t8a_pre V (ContinuousLinearMap.fst ℝ E E) (r26t8a_dY Ψ y)) x :=
    (r26t8a_pre V (ContinuousLinearMap.fst ℝ E E)).contDiff.contDiffAt.comp x h1
  have hf2 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun y => r26t8a_pre V (ContinuousLinearMap.snd ℝ E E) (r26t8a_dw Ψ y)) x :=
    (r26t8a_pre V (ContinuousLinearMap.snd ℝ E E)).contDiff.contDiffAt.comp x h2
  rw [fun_iteratedFDeriv_add_apply hf1 hf2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((r26t8a_pre V (ContinuousLinearMap.fst ℝ E E)).norm_iteratedFDeriv_comp_left h1 le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (r26t8a_pre_norm _ (ContinuousLinearMap.norm_fst_le ℝ E E))
  · refine ((r26t8a_pre V (ContinuousLinearMap.snd ℝ E E)).norm_iteratedFDeriv_comp_left h2 le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (r26t8a_pre_norm _ (ContinuousLinearMap.norm_snd_le ℝ E E))

end PartialY

end HRS.MS.R26T8A
