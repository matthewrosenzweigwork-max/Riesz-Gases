import HRS.Uniform.Q45Tens2

/-!
# Q45 (Lemma 3.20): density of elementary tensors
-/

noncomputable section

open MeasureTheory Filter Topology UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.Uniform.Q45

section Dense

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The closed set where two continuous linear maps agree contains `ProjTensor2 Y` once it contains the elementary
tensors. -/
lemma tensor_clm_ext {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A B : ProjTensor2 Y →L[ℝ] Z) (h : ∀ y y', A (tmul y y') = B (tmul y y')) : A = B := by
  ext τ
  refine Completion.induction_on τ (isClosed_eq A.continuous B.continuous) fun x => ?_
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r m
    have hc : (((r • PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y)) : ProjTensor2 Y) =
        r • tmul (m 0) (m 1) := by
      unfold tmul
      rw [tmulAlg_eq_tprod]
      exact Completion.coe_smul r _
    rw [hc, map_smul, map_smul, h]
  · intro x y hx hy
    rw [Completion.coe_add, map_add, map_add, hx, hy]

lemma update_cons0 (a c x : Y) : Function.update ![a, c] 0 x = ![x, c] := by
  funext i; fin_cases i <;> simp [Function.update]

lemma update_cons1 (a c x : Y) : Function.update ![a, c] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp [Function.update]

lemma tmulAlg_add_left (a b c : Y) : tmulAlg (a + b) c = tmulAlg a c + tmulAlg b c := by
  have := (PiTensorProduct.tprod ℝ (s := fun _ : Fin 2 => Y)).map_update_add ![a, c] 0 a b
  simpa only [update_cons0, tmulAlg] using this

lemma tmulAlg_add_right (a b c : Y) : tmulAlg a (b + c) = tmulAlg a b + tmulAlg a c := by
  have := (PiTensorProduct.tprod ℝ (s := fun _ : Fin 2 => Y)).map_update_add ![a, b] 1 b c
  simpa only [update_cons1, tmulAlg] using this

lemma tmulAlg_smul_left (r : ℝ) (a c : Y) : tmulAlg (r • a) c = r • tmulAlg a c := by
  have := (PiTensorProduct.tprod ℝ (s := fun _ : Fin 2 => Y)).map_update_smul ![a, c] 0 r a
  simpa only [update_cons0, tmulAlg] using this

lemma tmulAlg_smul_right (r : ℝ) (a c : Y) : tmulAlg a (r • c) = r • tmulAlg a c := by
  have := (PiTensorProduct.tprod ℝ (s := fun _ : Fin 2 => Y)).map_update_smul ![a, c] 1 r c
  simpa only [update_cons1, tmulAlg] using this

lemma tmulAlg_sub_left (a b c : Y) : tmulAlg (a - b) c = tmulAlg a c - tmulAlg b c := by
  have h : tmulAlg (a - b) c + tmulAlg b c = tmulAlg a c := by
    rw [← tmulAlg_add_left, sub_add_cancel]
  rw [← h]; abel

lemma tmulAlg_sub_right (a b c : Y) : tmulAlg a (b - c) = tmulAlg a b - tmulAlg a c := by
  have h : tmulAlg a (b - c) + tmulAlg a c = tmulAlg a b := by
    rw [← tmulAlg_add_right, sub_add_cancel]
  rw [← h]; abel

lemma tmul_add_left (a b c : Y) : tmul (a + b) c = tmul a c + tmul b c := by
  unfold tmul; rw [tmulAlg_add_left, Completion.coe_add]

lemma tmul_add_right (a b c : Y) : tmul a (b + c) = tmul a b + tmul a c := by
  unfold tmul; rw [tmulAlg_add_right, Completion.coe_add]

lemma tmul_smul_left (r : ℝ) (a c : Y) : tmul (r • a) c = r • tmul a c := by
  unfold tmul; rw [tmulAlg_smul_left, Completion.coe_smul]

lemma tmul_smul_right (r : ℝ) (a c : Y) : tmul a (r • c) = r • tmul a c := by
  unfold tmul; rw [tmulAlg_smul_right, Completion.coe_smul]

lemma tmul_sub_left (a b c : Y) : tmul (a - b) c = tmul a c - tmul b c := by
  unfold tmul; rw [tmulAlg_sub_left, Completion.coe_sub]

lemma tmul_sub_right (a b c : Y) : tmul a (b - c) = tmul a b - tmul a c := by
  unfold tmul; rw [tmulAlg_sub_right, Completion.coe_sub]

lemma norm_tmul_sub_le (a a' y y' : Y) :
    ‖tmul a a' - tmul y y'‖ ≤ ‖a - y‖ * ‖a'‖ + ‖y‖ * ‖a' - y'‖ := by
  have e : tmul a a' - tmul y y' = tmul (a - y) a' + tmul y (a' - y') := by
    rw [tmul_sub_left, tmul_sub_right]; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (norm_tmul_le _ _) (norm_tmul_le _ _))

end Dense

end HRS.Uniform.Q45
