import HRS.Uniform.Q45Sep1

/-!
# Q45 (Lemma 3.20): strong convergence of uniformly bounded tensor operators
-/

noncomputable section

open MeasureTheory Filter Topology UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.Uniform.Q45

section Conv

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma coe_smul_tprod (r : ℝ) (m : Fin 2 → Y) :
    (((r • PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y)) : ProjTensor2 Y) = r • tmul (m 0) (m 1) := by
  unfold tmul
  rw [tmulAlg_eq_tprod]
  exact Completion.coe_smul r _

lemma tensor_tendsto_of_bdd (Tn : ℕ → ProjTensor2 Y →L[ℝ] ProjTensor2 Y) {C : ℝ}
    (hb : ∀ n, ‖Tn n‖ ≤ C)
    (h : ∀ y y', Tendsto (fun n => Tn n (tmul y y')) atTop (𝓝 (tmul y y')))
    (τ : ProjTensor2 Y) : Tendsto (fun n => Tn n τ) atTop (𝓝 τ) := by
  have hC : 0 ≤ C := (norm_nonneg (Tn 0)).trans (hb 0)
  -- the algebraic tensors
  have halg : ∀ x : ⨂[ℝ] _ : Fin 2, Y,
      Tendsto (fun n => Tn n (x : ProjTensor2 Y)) atTop (𝓝 (x : ProjTensor2 Y)) := by
    intro x
    refine PiTensorProduct.induction_on x ?_ ?_
    · intro r m
      rw [coe_smul_tprod]
      simp only [map_smul]
      exact (h (m 0) (m 1)).const_smul r
    · intro x y hx hy
      simp only [Completion.coe_add, map_add]
      exact hx.add hy
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 (Completion.denseRange_coe (α := ⨂[ℝ] _ : Fin 2, Y)) τ _ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (halg x) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_eq_norm] at h1 hx ⊢
  have e : Tn n τ - τ = Tn n (τ - (x : ProjTensor2 Y)) + (Tn n (x : ProjTensor2 Y) - (x : ProjTensor2 Y)) +
      ((x : ProjTensor2 Y) - τ) := by
    rw [map_sub]; abel
  rw [e]
  have k1 : ‖Tn n (τ - (x : ProjTensor2 Y))‖ ≤ C * ‖τ - (x : ProjTensor2 Y)‖ :=
    (Tn n).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
  have k2 : ‖(x : ProjTensor2 Y) - τ‖ = ‖τ - (x : ProjTensor2 Y)‖ := norm_sub_rev _ _
  have k3 : (C + 1) * ‖τ - (x : ProjTensor2 Y)‖ ≤ (C + 1) * (ε / (2 * (C + 1))) :=
    mul_le_mul_of_nonneg_left hx.le (by positivity)
  have k4 : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by field_simp
  have k5 := norm_add₃_le (a := Tn n (τ - (x : ProjTensor2 Y)))
    (b := Tn n (x : ProjTensor2 Y) - (x : ProjTensor2 Y)) (c := (x : ProjTensor2 Y) - τ)
  linarith

end Conv

end HRS.Uniform.Q45
