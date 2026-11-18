import HRS.Uniform.Q45Smooth

/-!
# Q45 (Lemma 3.20): the projective tensor square of a normed space

API for `ProjTensor2 Y` (the completion of the projective tensor square): elementary tensors `tmul`, the pairing
`tensorPairing Ψ` as a continuous linear functional bounded by `‖Ψ‖`, and functoriality `tensorMap`.
-/

noncomputable section

open MeasureTheory Filter Topology UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.Uniform.Q45

section Tens

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The elementary tensor `y ⊗ y'` in the algebraic projective tensor square. -/
def tmulAlg (y y' : Y) : ⨂[ℝ] _ : Fin 2, Y := PiTensorProduct.tprod ℝ ![y, y']

/-- The elementary tensor `y ⊗ y'` in `ProjTensor2 Y`. -/
def tmul (y y' : Y) : ProjTensor2 Y := ((tmulAlg y y' : ⨂[ℝ] _ : Fin 2, Y) : ProjTensor2 Y)

lemma norm_tmul_le (y y' : Y) : ‖tmul y y'‖ ≤ ‖y‖ * ‖y'‖ := by
  unfold tmul
  rw [Completion.norm_coe]
  have := PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℝ) (E := fun _ : Fin 2 => Y) ![y, y']
  simpa [tmulAlg, Fin.prod_univ_two] using this

/-- The pairing form as a continuous multilinear map. -/
def pairCM (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ :=
  (bilinMultilinear Ψ).mkContinuous ‖Ψ‖ (fun v => by
    simp only [bilinMultilinear, MultilinearMap.coe_mk, Fin.prod_univ_two]
    calc ‖Ψ (v 0) (v 1)‖ ≤ ‖Ψ (v 0)‖ * ‖v 1‖ := (Ψ (v 0)).le_opNorm _
      _ ≤ (‖Ψ‖ * ‖v 0‖) * ‖v 1‖ := by gcongr; exact Ψ.le_opNorm _
      _ = ‖Ψ‖ * (‖v 0‖ * ‖v 1‖) := by ring)

/-- The pairing as a continuous linear functional on the algebraic projective tensor square. -/
def pairL (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : (⨂[ℝ] _ : Fin 2, Y) →L[ℝ] ℝ :=
  PiTensorProduct.liftEquiv ℝ (fun _ : Fin 2 => Y) ℝ (pairCM Ψ)

lemma pairL_apply (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (x : ⨂[ℝ] _ : Fin 2, Y) :
    pairL Ψ x = PiTensorProduct.lift (bilinMultilinear Ψ) x := rfl

lemma norm_pairCM_le (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : ‖pairCM Ψ‖ ≤ ‖Ψ‖ :=
  MultilinearMap.mkContinuous_norm_le _ (show 0 ≤ ‖Ψ‖ from norm_nonneg Ψ) _

lemma norm_pairL_le (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (x : ⨂[ℝ] _ : Fin 2, Y) : ‖pairL Ψ x‖ ≤ ‖Ψ‖ * ‖x‖ := by
  have := PiTensorProduct.norm_eval_le_projectiveSeminorm (pairCM Ψ) x
  have e : (PiTensorProduct.lift (pairCM Ψ).toMultilinearMap) x = pairL Ψ x := rfl
  rw [e] at this
  exact this.trans (mul_le_mul_of_nonneg_right (norm_pairCM_le Ψ) (norm_nonneg _))

lemma pairL_tmulAlg (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (y y' : Y) : pairL Ψ (tmulAlg y y') = Ψ y y' := by
  unfold tmulAlg
  rw [pairL_apply, PiTensorProduct.lift.tprod]
  rfl

/-- The pairing with a bounded bilinear form, as a continuous linear functional on `ProjTensor2 Y`. -/
def tensorPairingL (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : ProjTensor2 Y →L[ℝ] ℝ := (pairL Ψ).fromCompletion

lemma tensorPairingL_coe (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (x : ⨂[ℝ] _ : Fin 2, Y) :
    tensorPairingL Ψ (x : ProjTensor2 Y) = pairL Ψ x :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

lemma tensorPairing_eq (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : tensorPairing Ψ = ⇑(tensorPairingL Ψ) := by
  unfold tensorPairing tensorPairingL
  rw [ContinuousLinearMap.coe_fromCompletion]
  rfl

lemma tensorPairing_tmul (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (y y' : Y) : tensorPairing Ψ (tmul y y') = Ψ y y' := by
  rw [tensorPairing_eq]
  unfold tmul
  rw [tensorPairingL_coe, pairL_tmulAlg]

lemma norm_tensorPairing_le (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (τ : ProjTensor2 Y) :
    ‖tensorPairingL Ψ τ‖ ≤ ‖Ψ‖ * ‖τ‖ := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · exact isClosed_le (continuous_norm.comp (tensorPairingL Ψ).continuous)
      (continuous_const.mul continuous_norm)
  · rw [tensorPairingL_coe, Completion.norm_coe]
    exact norm_pairL_le Ψ x

end Tens

end HRS.Uniform.Q45
