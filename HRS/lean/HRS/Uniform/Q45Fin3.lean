import HRS.Uniform.Q45Fin2

/-!
# Q45: the common finite-dimensional subspace carrying all block directions
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_block_data {m : ℕ} (Nb : ℕ) (α : Fin m → ℕ → H) :
    ∃ (q : ℕ) (fH : Fin q → H) (A : ℕ → Matrix (Fin m) (Fin q) ℝ), Orthonormal ℝ fH ∧
      (∀ k, Nb ≤ k → A k = 0) ∧
      (∀ k < Nb, ∀ j v, ∑ c, A k j c * inner ℝ (fH c) v = inner ℝ (α j k) v) ∧
      (∀ k < Nb, ∀ j (u : Fin q → ℝ), (A k).mulVec u j = inner ℝ (α j k) (∑ c, u c • fH c)) := by
  classical
  set F : Submodule ℝ H := Submodule.span ℝ (Set.range fun p : Fin m × Fin Nb => α p.1 p.2) with hF
  haveI : FiniteDimensional ℝ F := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  set f := stdOrthonormalBasis ℝ F with hf
  have hon : Orthonormal ℝ (fun c => ((f c : F) : H)) :=
    f.orthonormal.comp_linearIsometry F.subtypeₗᵢ
  refine ⟨Module.finrank ℝ F, fun c => ((f c : F) : H),
    fun k j c => if k < Nb then inner ℝ (α j k) ((f c : F) : H) else 0, hon, ?_, ?_, ?_⟩
  · intro k hk
    ext j c
    simp [not_lt.2 hk]
  · intro k hk j v
    have hmem : α j k ∈ F := Submodule.subset_span ⟨(j, ⟨k, hk⟩), rfl⟩
    have := f.sum_repr' (⟨α j k, hmem⟩ : F)
    have h2 := congrArg (fun a : F => inner ℝ (a : H) v) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, sum_inner, real_inner_smul_left] at h2
    simp only [hk, if_true]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [real_inner_comm ((f c : F) : H) (α j k)]
    rfl
  · intro k hk j u
    simp only [Matrix.mulVec, dotProduct, hk, if_true, inner_sum, real_inner_smul_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

end HRS.Uniform.Q45
