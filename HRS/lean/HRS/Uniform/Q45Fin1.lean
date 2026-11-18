import HRS.Uniform.Q45Path2

/-!
# Q45: matrix helper lemmas for the finite-dimensional comparison
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

lemma mulVec_sq_le_frob {m q : ℕ} (A : Matrix (Fin m) (Fin q) ℝ) (u : Fin q → ℝ) :
    (A.mulVec u) ⬝ᵥ (A.mulVec u) ≤ (∑ j, ∑ c, A j c ^ 2) * (u ⬝ᵥ u) := by
  have h : ∀ j, (A.mulVec u j) ^ 2 ≤ (∑ c, A j c ^ 2) * (u ⬝ᵥ u) := by
    intro j
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => A j c) u
    simpa [Matrix.mulVec, dotProduct, sq] using this
  calc (A.mulVec u) ⬝ᵥ (A.mulVec u) = ∑ j, (A.mulVec u j) ^ 2 := by simp [dotProduct, sq]
    _ ≤ ∑ j, (∑ c, A j c ^ 2) * (u ⬝ᵥ u) := Finset.sum_le_sum fun j _ => h j
    _ = _ := by rw [Finset.sum_mul]

/-- `ν_ρ` of a conjugated matrix. -/
lemma nu_conj_le {m q : ℕ} {ρ : (Fin m → ℝ) → ℝ} (hρ : ∀ u, 0 ≤ ρ u) (A : Matrix (Fin m) (Fin q) ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ u : Fin q → ℝ, ρ (A.mulVec u) ≤ K * Real.sqrt (u ⬝ᵥ u))
    (S : Matrix (Fin q) (Fin q) ℝ) : nuRho ρ (A * S * Aᵀ) ≤ K ^ 2 * traceNormMatrix S := by
  classical
  unfold nuRho
  refine Real.iSup_le (fun H => ?_) (mul_nonneg (sq_nonneg K) (by
    have := traceNormMatrix_nonneg S; exact this))
  set Hm : Matrix (Fin m) (Fin m) ℝ := (H : Matrix (Fin m) (Fin m) ℝ) with hHm
  set H' : Matrix (Fin q) (Fin q) ℝ := Aᵀ * Hm * A with hH'
  have e : ∑ a, ∑ b, Hm a b * (A * S * Aᵀ) a b = ∑ a, ∑ b, H' a b * S a b := by
    have : Matrix.trace ((A * S * Aᵀ)ᵀ * Hm) = Matrix.trace (Sᵀ * H') := by
      simp only [hH', Matrix.transpose_mul, Matrix.transpose_transpose]
      calc _ = Matrix.trace (A * (Sᵀ * (Aᵀ * Hm))) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace ((Sᵀ * (Aᵀ * Hm)) * A) := Matrix.trace_mul_comm _ _
        _ = _ := by simp [Matrix.mul_assoc]
    have h1 : ∑ a, ∑ b, Hm a b * (A * S * Aᵀ) a b = Matrix.trace ((A * S * Aᵀ)ᵀ * Hm) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have h2 : Matrix.trace (Sᵀ * H') = ∑ a, ∑ b, H' a b * S a b := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h1, this, h2]
  rw [e]
  have hβ : ∀ u v : Fin q → ℝ, |u ⬝ᵥ (H'.mulVec v)| ≤
      K ^ 2 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
    intro u v
    have h1 : u ⬝ᵥ (H'.mulVec v) = (A.mulVec u) ⬝ᵥ (Hm.mulVec (A.mulVec v)) := by
      simp only [hH', ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h1]
    refine (H.2 _ _).trans ?_
    calc ρ (A.mulVec u) * ρ (A.mulVec v) ≤ (K * Real.sqrt (u ⬝ᵥ u)) * (K * Real.sqrt (v ⬝ᵥ v)) :=
          mul_le_mul (hA u) (hA v) (hρ _) (by positivity)
      _ = K ^ 2 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring
  exact trace_dual H' S (K ^ 2) (sq_nonneg K) hβ

end HRS.Uniform.Q45
