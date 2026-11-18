import HRS.Uniform.Q45Lind5

/-!
# Q45: matrix facts (trace norm of a conjugated matrix)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

lemma dot_sq_le {n : ℕ} (x y : Fin n → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [dotProduct, sq] using this

lemma abs_dot_le {n : ℕ} (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have h1 : 0 ≤ x ⬝ᵥ x := by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : 0 ≤ y ⬝ᵥ y := by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [← Real.sqrt_mul h1]
  exact Real.abs_le_sqrt (dot_sq_le x y)

lemma orth_dot_self {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (w : Fin n → ℝ) :
    ((U : Matrix (Fin n) (Fin n) ℝ).mulVec w) ⬝ᵥ ((U : Matrix (Fin n) (Fin n) ℝ).mulVec w) = w ⬝ᵥ w := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
    simpa using this
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- Conjugation by a matrix of operator norm at most `c` multiplies the trace norm by at most `c²`. -/
lemma s1Norm_conj_le {m q : ℕ} (A : Matrix (Fin m) (Fin q) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ u : Fin q → ℝ, (A.mulVec u) ⬝ᵥ (A.mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u))
    (S : Matrix (Fin q) (Fin q) ℝ) :
    traceNormMatrix (A * S * Aᵀ) ≤ c ^ 2 * traceNormMatrix S := by
  classical
  unfold traceNormMatrix
  have hne : Nonempty (Matrix.orthogonalGroup (Fin m) ℝ) := ⟨1⟩
  refine ciSup_le fun U => ?_
  set Um : Matrix (Fin m) (Fin m) ℝ := (U : Matrix (Fin m) (Fin m) ℝ) with hUm
  set H : Matrix (Fin q) (Fin q) ℝ := Aᵀ * Um * A with hH
  have e : Matrix.trace ((A * S * Aᵀ)ᵀ * Um) = ∑ a, ∑ b, H a b * S a b := by
    have : Matrix.trace ((A * S * Aᵀ)ᵀ * Um) = Matrix.trace (Sᵀ * H) := by
      simp only [hH, Matrix.transpose_mul, Matrix.transpose_transpose]
      calc _ = Matrix.trace (A * (Sᵀ * (Aᵀ * Um))) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace ((Sᵀ * (Aᵀ * Um)) * A) := Matrix.trace_mul_comm _ _
        _ = _ := by simp [Matrix.mul_assoc]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e]
  have hβ : ∀ u v : Fin q → ℝ, |u ⬝ᵥ (H.mulVec v)| ≤
      c ^ 2 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
    intro u v
    have h1 : u ⬝ᵥ (H.mulVec v) = (A.mulVec u) ⬝ᵥ (Um.mulVec (A.mulVec v)) := by
      simp only [hH, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h1]
    refine (abs_dot_le _ _).trans ?_
    rw [orth_dot_self U]
    have s1 : Real.sqrt ((A.mulVec u) ⬝ᵥ (A.mulVec u)) ≤ c * Real.sqrt (u ⬝ᵥ u) := by
      calc _ ≤ Real.sqrt (c ^ 2 * (u ⬝ᵥ u)) := Real.sqrt_le_sqrt (hA u)
        _ = c * Real.sqrt (u ⬝ᵥ u) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
    have s2 : Real.sqrt ((A.mulVec v) ⬝ᵥ (A.mulVec v)) ≤ c * Real.sqrt (v ⬝ᵥ v) := by
      calc _ ≤ Real.sqrt (c ^ 2 * (v ⬝ᵥ v)) := Real.sqrt_le_sqrt (hA v)
        _ = c * Real.sqrt (v ⬝ᵥ v) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
    calc _ ≤ (c * Real.sqrt (u ⬝ᵥ u)) * (c * Real.sqrt (v ⬝ᵥ v)) :=
          mul_le_mul s1 s2 (Real.sqrt_nonneg _) (by positivity)
      _ = c ^ 2 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring
  exact (le_abs_self _).trans (trace_dual H S (c ^ 2) (sq_nonneg c) hβ)

end HRS.Uniform.Q45
