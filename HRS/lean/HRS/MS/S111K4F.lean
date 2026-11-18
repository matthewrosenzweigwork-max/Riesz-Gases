import HRS.MS.S111K4E

/-!
# S11.1 / T01 (S11K4), part F: the finite Wick difference theorem
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HRS.MS.S111K4

theorem k4_lin_comb {ι : Type*} [Fintype ι] {m : ℕ} (r : Fin m → ι → ℝ) (x : Fin m → ℝ) (g : ι → ℝ) :
    ∑ i, x i * ∑ k, r i k * g k = ∑ k, (∑ i, r i k * x i) * g k := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- Finite-dimensional Wick difference of two jointly Gaussian families sharing the matrix `A`. -/
theorem k4_finite_wick {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ)
    (X : Ω → (Fin 2 × Fin m) → ℝ) (hX : AEMeasurable X P) (hG : HRS.IsCenteredGaussian (P.map X)) (B δ : ℝ)
    (hS : ∀ c : Fin m → ℝ, ∫ ω, (∑ i, c i * X ω (0, i)) ^ 2 ∂P ≤ B ^ 2 * ∑ i, c i ^ 2)
    (hS' : ∀ c : Fin m → ℝ, ∫ ω, (∑ i, c i * X ω (1, i)) ^ 2 ∂P ≤ B ^ 2 * ∑ i, c i ^ 2)
    (hD : ∀ c : Fin m → ℝ, ∫ ω, (∑ i, c i * (X ω (0, i) - X ω (1, i))) ^ 2 ∂P ≤ δ ^ 2 * ∑ i, c i ^ 2)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    ∫ ω, ((∑ i, ∑ j, A i j * (X ω (0, i) * X ω (0, j) - ∫ η, X η (0, i) * X η (0, j) ∂P)) -
        ∑ i, ∑ j, A i j * (X ω (1, i) * X ω (1, j) - ∫ η, X η (1, i) * X η (1, j) ∂P)) ^ 2 ∂P ≤
      8 * B ^ 2 * δ ^ 2 * k4fr A := by
  classical
  obtain ⟨R, hR⟩ := k4_rep P X hX hG
  have hRc : Continuous fun g : Fin 2 × Fin m → ℝ => R.mulVec g :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hlaw : ∀ F : (Fin 2 × Fin m → ℝ) → ℝ, Continuous F →
      ∫ ω, F (X ω) ∂P = ∫ g, F (R.mulVec g) ∂(k4gm (Fin 2 × Fin m)) := by
    intro F hF
    rw [← integral_map hX hF.aestronglyMeasurable, hR,
      integral_map hRc.measurable.aemeasurable hF.aestronglyMeasurable]
  have hm : ∀ a b, ∫ η, X η a * X η b ∂P = ∑ k, R a k * R b k := by
    intro a b
    rw [hlaw (fun x => x a * x b) (by fun_prop)]
    exact k4_linear_mul (R a) (R b)
  set S : Matrix (Fin 2 × Fin m) (Fin m) ℝ := Matrix.of fun k i => R (0, i) k with hSdef
  set S' : Matrix (Fin 2 × Fin m) (Fin m) ℝ := Matrix.of fun k i => R (1, i) k with hS'def
  have hRg0 : ∀ (g : Fin 2 × Fin m → ℝ) i, R.mulVec g (0, i) = ∑ k, S k i * g k := fun g i => by
    simp [Matrix.mulVec, dotProduct, hSdef]
  have hRg1 : ∀ (g : Fin 2 × Fin m → ℝ) i, R.mulVec g (1, i) = ∑ k, S' k i * g k := fun g i => by
    simp [Matrix.mulVec, dotProduct, hS'def]
  have hSop : ∀ x : Fin m → ℝ, ∑ k, (∑ i, S k i * x i) ^ 2 ≤ B ^ 2 * ∑ i, x i ^ 2 := by
    intro x
    have h := hS x
    rw [hlaw (fun y => (∑ i, x i * y (0, i)) ^ 2) (by fun_prop)] at h
    have e : ∀ g : Fin 2 × Fin m → ℝ, (∑ i, x i * R.mulVec g (0, i)) = ∑ k, (∑ i, S k i * x i) * g k := by
      intro g
      simp only [hRg0]
      exact k4_lin_comb (fun i k => S k i) x g
    simp_rw [e] at h
    rwa [k4_linear_sq (fun k => ∑ i, S k i * x i)] at h
  have hSop' : ∀ x : Fin m → ℝ, ∑ k, (∑ i, S' k i * x i) ^ 2 ≤ B ^ 2 * ∑ i, x i ^ 2 := by
    intro x
    have h := hS' x
    rw [hlaw (fun y => (∑ i, x i * y (1, i)) ^ 2) (by fun_prop)] at h
    have e : ∀ g : Fin 2 × Fin m → ℝ, (∑ i, x i * R.mulVec g (1, i)) = ∑ k, (∑ i, S' k i * x i) * g k := by
      intro g
      simp only [hRg1]
      exact k4_lin_comb (fun i k => S' k i) x g
    simp_rw [e] at h
    rwa [k4_linear_sq (fun k => ∑ i, S' k i * x i)] at h
  have hDop : ∀ x : Fin m → ℝ, ∑ k, (∑ i, (S k i - S' k i) * x i) ^ 2 ≤ δ ^ 2 * ∑ i, x i ^ 2 := by
    intro x
    have h := hD x
    rw [hlaw (fun y => (∑ i, x i * (y (0, i) - y (1, i))) ^ 2) (by fun_prop)] at h
    have e : ∀ g : Fin 2 × Fin m → ℝ,
        (∑ i, x i * (R.mulVec g (0, i) - R.mulVec g (1, i))) = ∑ k, (∑ i, (S k i - S' k i) * x i) * g k := by
      intro g
      simp only [hRg0, hRg1, ← Finset.sum_sub_distrib, ← sub_mul]
      exact k4_lin_comb (fun i k => S k i - S' k i) x g
    simp_rw [e] at h
    rwa [k4_linear_sq (fun k => ∑ i, (S k i - S' k i) * x i)] at h
  have hM := k4fr_transport S S' A B δ hSop hSop' hDop
  set M : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℝ := S * A * Sᵀ - S' * A * S'ᵀ with hMdef
  have hpt : ∀ g : Fin 2 × Fin m → ℝ,
      ((∑ i, ∑ j, A i j * (R.mulVec g (0, i) * R.mulVec g (0, j) -
          ∫ η, X η (0, i) * X η (0, j) ∂P)) -
        ∑ i, ∑ j, A i j * (R.mulVec g (1, i) * R.mulVec g (1, j) -
          ∫ η, X η (1, i) * X η (1, j) ∂P)) = g ⬝ᵥ (M.mulVec g) - M.trace := by
    intro g
    have c0 : ∀ i j, ∫ η, X η (0, i) * X η (0, j) ∂P = ∑ k, S k i * S k j := fun i j => by
      rw [hm]; rfl
    have c1 : ∀ i j, ∫ η, X η (1, i) * X η (1, j) ∂P = ∑ k, S' k i * S' k j := fun i j => by
      rw [hm]; rfl
    simp only [c0, c1, hRg0, hRg1, mul_sub, Finset.sum_sub_distrib]
    rw [k4_quad_expand S A g, k4_quad_expand S' A g, k4_trace_expand S A, k4_trace_expand S' A]
    simp only [hMdef, Matrix.sub_mulVec, dotProduct_sub, Matrix.trace_sub]
    ring
  calc ∫ ω, ((∑ i, ∑ j, A i j * (X ω (0, i) * X ω (0, j) - ∫ η, X η (0, i) * X η (0, j) ∂P)) -
        ∑ i, ∑ j, A i j * (X ω (1, i) * X ω (1, j) - ∫ η, X η (1, i) * X η (1, j) ∂P)) ^ 2 ∂P
      = ∫ g, (g ⬝ᵥ (M.mulVec g) - M.trace) ^ 2 ∂(k4gm (Fin 2 × Fin m)) := by
        rw [hlaw (fun x => ((∑ i, ∑ j, A i j * (x (0, i) * x (0, j) - ∫ η, X η (0, i) * X η (0, j) ∂P)) -
          ∑ i, ∑ j, A i j * (x (1, i) * x (1, j) - ∫ η, X η (1, i) * X η (1, j) ∂P)) ^ 2) (by fun_prop)]
        simp_rw [hpt]
    _ ≤ 2 * k4fr M := k4_quad_L2_le M
    _ ≤ 8 * B ^ 2 * δ ^ 2 * k4fr A := by nlinarith [hM]

end HRS.MS.S111K4
