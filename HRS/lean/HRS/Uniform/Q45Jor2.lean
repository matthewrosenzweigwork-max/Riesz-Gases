import HRS.Uniform.Q45Jor1

/-!
# Q45 (Lemma 3.20): Jordan decomposition, trace bounds
-/

noncomputable section

open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Basis

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Hilbert basis of `H` each of whose vectors lies in a given closed subspace `K` or in `Kᗮ`. -/
lemma exists_adapted_basis (K : Submodule ℝ H) (hK : IsClosed (K : Set H)) :
    ∃ (w : Set H) (b : HilbertBasis w ℝ H), ⇑b = ((↑) : w → H) ∧ ∀ e ∈ w, e ∈ K ∨ e ∈ Kᗮ := by
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨wK, bK, hbK⟩ := exists_hilbertBasis ℝ K
  set v : wK → H := fun i => ((i : K) : H) with hv
  have hvinj : Function.Injective v := fun i j h => Subtype.ext (Subtype.ext h)
  have hvon : Orthonormal ℝ v := by
    have h := bK.orthonormal.comp_linearIsometry K.subtypeₗᵢ
    have e : (K.subtypeₗᵢ ∘ ⇑bK) = v := by funext i; simp [hv, hbK]
    rwa [e] at h
  have hs : Orthonormal ℝ ((↑) : Set.range v → H) := (orthonormal_subtype_range hvinj).2 hvon
  obtain ⟨w, b, hsw, hb⟩ := hs.exists_hilbertBasis_extension
  have hon : Orthonormal ℝ ((↑) : w → H) := hb ▸ b.orthonormal
  refine ⟨w, b, hb, fun e he => ?_⟩
  by_cases hes : e ∈ Set.range v
  · obtain ⟨i, rfl⟩ := hes
    exact Or.inl (i : K).2
  · right
    rw [Submodule.mem_orthogonal]
    intro k hk
    have hzero : ∀ i : wK, inner ℝ e (v i) = 0 := by
      intro i
      have hne : (⟨e, he⟩ : w) ≠ ⟨v i, hsw ⟨i, rfl⟩⟩ := fun h => hes ⟨i, by simpa using (congrArg Subtype.val h).symm⟩
      exact hon.inner_eq_zero hne
    have hsum := bK.hasSum_repr ⟨k, hk⟩
    have h2 := hsum.mapL ((innerSL ℝ e).comp K.subtypeL)
    have h3 : (fun i : wK => ((innerSL ℝ e).comp K.subtypeL) (bK.repr ⟨k, hk⟩ i • bK i)) = fun _ => 0 := by
      funext i
      simp only [ContinuousLinearMap.comp_apply, map_smul, Submodule.subtypeL_apply, innerSL_apply_apply,
        smul_eq_mul]
      have : ((bK i : K) : H) = v i := by simp [hv, hbK]
      rw [this, hzero i, mul_zero]
    rw [h3] at h2
    have h4 := hasSum_zero.unique h2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply] at h4
    rw [real_inner_comm]
    exact h4.symm

end Basis

end HRS.Uniform.Q45
