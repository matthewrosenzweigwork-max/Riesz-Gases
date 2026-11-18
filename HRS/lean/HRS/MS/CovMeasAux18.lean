import HRS.MS.CovMeasAux17

/-!
# S10.1 (worker S101B), part 18: the bridge `ProjTensor2 Y → projTensor Y 2`

`ProjTensor2 Y` (completion of the algebraic projective tensor square, used by the torus covariance measure) and the frozen
`projTensor Y 2` (closure of the elementary tensors in `TensorDual Y 2 = (Y[×2]→L ℝ)'`) are connected by
`s101Bri τ = (M ↦ ⟨M, τ⟩)`: `s101Bri (tmul y y') = elemTensor ![y,y']`, `s101Bri` is linear with `‖s101Bri τ‖ ≤ ‖τ‖`, and lands in
`projTensor Y 2`.  The pairing `tensorPairing Ψ τ` is linear in the bilinear form `Ψ` (`s101_tensorPairingL_add`, `_smul`).
-/

noncomputable section

set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45

section Bridge

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma s101_pairL_add (Ψ₁ Ψ₂ : Y →L[ℝ] Y →L[ℝ] ℝ) : pairL (Ψ₁ + Ψ₂) = pairL Ψ₁ + pairL Ψ₂ := by
  refine ContinuousLinearMap.coe_injective (PiTensorProduct.ext (MultilinearMap.ext fun m => ?_))
  have e1 : (PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y) = tmulAlg (m 0) (m 1) :=
    (tmulAlg_eq_tprod m).symm
  simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
    LinearMap.add_apply]
  rw [e1, pairL_tmulAlg, pairL_tmulAlg, pairL_tmulAlg]
  rfl

lemma s101_pairL_smul (a : ℝ) (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : pairL (a • Ψ) = a • pairL Ψ := by
  refine ContinuousLinearMap.coe_injective (PiTensorProduct.ext (MultilinearMap.ext fun m => ?_))
  have e1 : (PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y) = tmulAlg (m 0) (m 1) :=
    (tmulAlg_eq_tprod m).symm
  simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
    LinearMap.smul_apply]
  rw [e1, pairL_tmulAlg, pairL_tmulAlg]
  rfl

lemma s101_tensorPairingL_add (Ψ₁ Ψ₂ : Y →L[ℝ] Y →L[ℝ] ℝ) (τ : ProjTensor2 Y) :
    tensorPairingL (Ψ₁ + Ψ₂) τ = tensorPairingL Ψ₁ τ + tensorPairingL Ψ₂ τ := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · exact isClosed_eq (tensorPairingL _).continuous
      ((tensorPairingL Ψ₁).continuous.add (tensorPairingL Ψ₂).continuous)
  · rw [tensorPairingL_coe, tensorPairingL_coe, tensorPairingL_coe, s101_pairL_add]
    rfl

lemma s101_tensorPairingL_smul (a : ℝ) (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (τ : ProjTensor2 Y) :
    tensorPairingL (a • Ψ) τ = a * tensorPairingL Ψ τ := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · exact isClosed_eq (tensorPairingL _).continuous (continuous_const.mul (tensorPairingL Ψ).continuous)
  · rw [tensorPairingL_coe, tensorPairingL_coe, s101_pairL_smul]
    rfl

lemma s101_update0 (y z w : Y) : Function.update ![y, z] 0 w = ![w, z] := by
  funext i; fin_cases i <;> simp [Function.update]

lemma s101_update1 (y z w : Y) : Function.update ![y, z] 1 w = ![y, w] := by
  funext i; fin_cases i <;> simp [Function.update]

/-- The bilinear form `(y,y') ↦ M ![y,y']` of a bounded bilinear form given as a multilinear map. -/
def s101curry (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) : Y →L[ℝ] Y →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun y y' => M ![y, y'])
      (fun y y' z => by
        have h := M.toMultilinearMap.map_update_add ![y, z] 0 y y'
        rw [s101_update0, s101_update0, s101_update0] at h
        exact h)
      (fun a y z => by
        have h := M.toMultilinearMap.map_update_smul ![y, z] 0 a y
        rw [s101_update0, s101_update0] at h
        exact h)
      (fun y z z' => by
        have h := M.toMultilinearMap.map_update_add ![y, z] 1 z z'
        rw [s101_update1, s101_update1, s101_update1] at h
        exact h)
      (fun a y z => by
        have h := M.toMultilinearMap.map_update_smul ![y, z] 1 a z
        rw [s101_update1, s101_update1] at h
        exact h))
    ‖M‖ (fun y y' => by
      have := M.le_opNorm ![y, y']
      simpa [Fin.prod_univ_two, mul_assoc] using this)

lemma s101curry_apply (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) (y y' : Y) :
    s101curry M y y' = M ![y, y'] := rfl

lemma s101curry_add (M M' : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) :
    s101curry (M + M') = s101curry M + s101curry M' := by
  ext y y'; simp [s101curry_apply]

lemma s101curry_smul (a : ℝ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) :
    s101curry (a • M) = a • s101curry M := by
  ext y y'; simp [s101curry_apply]

lemma norm_s101curry_le (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) : ‖s101curry M‖ ≤ ‖M‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg M) _


/-- The embedding `τ ↦ (M ↦ ⟨M, τ⟩)` of `ProjTensor2 Y` into `TensorDual Y 2`. -/
def s101Bri (τ : ProjTensor2 Y) : TensorDual Y 2 :=
  LinearMap.mkContinuous
    { toFun := fun M => tensorPairingL (s101curry M) τ
      map_add' := fun M M' => by rw [s101curry_add, s101_tensorPairingL_add]
      map_smul' := fun a M => by
        rw [s101curry_smul, s101_tensorPairingL_smul]; rfl }
    ‖τ‖ (fun M => by
      show ‖tensorPairingL (s101curry M) τ‖ ≤ ‖τ‖ * ‖M‖
      calc ‖tensorPairingL (s101curry M) τ‖ ≤ ‖s101curry M‖ * ‖τ‖ := norm_tensorPairing_le _ _
        _ ≤ ‖M‖ * ‖τ‖ := mul_le_mul_of_nonneg_right (norm_s101curry_le M) (norm_nonneg _)
        _ = ‖τ‖ * ‖M‖ := mul_comm _ _)

lemma s101Bri_apply (τ : ProjTensor2 Y) (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ) :
    s101Bri τ M = tensorPairingL (s101curry M) τ := rfl

lemma s101Bri_add (τ τ' : ProjTensor2 Y) : s101Bri (τ + τ') = s101Bri τ + s101Bri τ' := by
  ext M; simp [s101Bri_apply]

lemma s101Bri_smul (a : ℝ) (τ : ProjTensor2 Y) : s101Bri (a • τ) = a • s101Bri τ := by
  ext M; simp [s101Bri_apply]

lemma s101Bri_sub (τ τ' : ProjTensor2 Y) : s101Bri (τ - τ') = s101Bri τ - s101Bri τ' := by
  ext M; simp [s101Bri_apply]

lemma norm_s101Bri_le (τ : ProjTensor2 Y) : ‖s101Bri τ‖ ≤ ‖τ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg τ) _

lemma s101Bri_tmul (y y' : Y) : s101Bri (tmul y y') = elemTensor ![y, y'] := by
  ext M
  rw [s101Bri_apply, ← tensorPairing_eq, tensorPairing_tmul, s101curry_apply]
  rfl

lemma lipschitz_s101Bri : LipschitzWith 1 (s101Bri : ProjTensor2 Y → TensorDual Y 2) := by
  refine LipschitzWith.of_dist_le_mul fun τ τ' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← s101Bri_sub]
  simpa using norm_s101Bri_le (τ - τ')

end Bridge

section Mem

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y]

lemma elemTensor_mem_projTensor (v : Fin 2 → Y) : elemTensor v ∈ projTensor Y 2 :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span (Set.mem_range_self v))

theorem s101Bri_mem (τ : ProjTensor2 Y) : s101Bri τ ∈ projTensor Y 2 := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · have hcl : IsClosed ((projTensor Y 2 : Submodule ℝ (TensorDual Y 2)) : Set (TensorDual Y 2)) :=
      Submodule.isClosed_topologicalClosure _
    exact hcl.preimage lipschitz_s101Bri.continuous
  · refine PiTensorProduct.induction_on x ?_ ?_
    · intro r m
      have e : ((r • PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y) : ProjTensor2 Y) =
          r • tmul (m 0) (m 1) := by
        rw [Completion.coe_smul]
        congr 1
        unfold tmul
        rw [tmulAlg_eq_tprod]
      rw [e, s101Bri_smul, s101Bri_tmul]
      have : (![m 0, m 1] : Fin 2 → Y) = m := by funext i; fin_cases i <;> rfl
      rw [this]
      exact (projTensor Y 2).smul_mem r (elemTensor_mem_projTensor m)
    · intro a b ha hb
      rw [Completion.coe_add, s101Bri_add]
      exact (projTensor Y 2).add_mem ha hb

end Mem

end HRS.MS.CovMeas
