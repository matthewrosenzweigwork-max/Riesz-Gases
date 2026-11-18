import HRS.Uniform.Q45Tens1

/-!
# Q45 (Lemma 3.20): functoriality of the projective tensor square and a density principle
-/

noncomputable section

open MeasureTheory Filter Topology UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.Uniform.Q45

section Tens2

variable {Y Y' : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Y']
  [NormedSpace ℝ Y']

lemma tmulAlg_eq_tprod (m : Fin 2 → Y) : tmulAlg (m 0) (m 1) = PiTensorProduct.tprod ℝ m := by
  unfold tmulAlg
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The functorial action `f ⊗ f` on the projective tensor square. -/
def tensorMap (f : Y →L[ℝ] Y') : ProjTensor2 Y →L[ℝ] ProjTensor2 Y' :=
  (PiTensorProduct.mapL (fun _ : Fin 2 => f)).completion

lemma tensorMap_coe (f : Y →L[ℝ] Y') (x : ⨂[ℝ] _ : Fin 2, Y) :
    tensorMap f (x : ProjTensor2 Y) = ((PiTensorProduct.mapL (fun _ : Fin 2 => f) x : ⨂[ℝ] _ : Fin 2, Y') : ProjTensor2 Y') :=
  ContinuousLinearMap.completion_apply_coe _ _

lemma tensorMap_tmul (f : Y →L[ℝ] Y') (y y' : Y) : tensorMap f (tmul y y') = tmul (f y) (f y') := by
  unfold tmul
  rw [tensorMap_coe, PiTensorProduct.mapL_apply]
  congr 1
  unfold tmulAlg
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

lemma norm_tensorMap_le (f : Y →L[ℝ] Y') (τ : ProjTensor2 Y) : ‖tensorMap f τ‖ ≤ ‖f‖ ^ 2 * ‖τ‖ := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · exact isClosed_le (continuous_norm.comp (tensorMap f).continuous) (continuous_const.mul continuous_norm)
  · rw [tensorMap_coe, Completion.norm_coe, Completion.norm_coe]
    have h1 := (PiTensorProduct.mapL (fun _ : Fin 2 => f)).le_opNorm x
    have h2 := PiTensorProduct.opNorm_mapL (fun _ : Fin 2 => f)
    simp only [Fin.prod_univ_two] at h2
    calc ‖PiTensorProduct.mapL (fun _ : Fin 2 => f) x‖
        ≤ ‖PiTensorProduct.mapL (fun _ : Fin 2 => f)‖ * ‖x‖ := h1
      _ ≤ (‖f‖ * ‖f‖) * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖f‖ ^ 2 * ‖x‖ := by ring

lemma tensorPairing_tensorMap (Ψ : Y' →L[ℝ] Y' →L[ℝ] ℝ) (f : Y →L[ℝ] Y') (τ : ProjTensor2 Y) :
    tensorPairingL Ψ (tensorMap f τ) = tensorPairingL (Ψ.bilinearComp f f) τ := by
  refine Completion.induction_on τ ?_ fun x => ?_
  · exact isClosed_eq ((tensorPairingL Ψ).continuous.comp (tensorMap f).continuous)
      (tensorPairingL _).continuous
  · rw [tensorMap_coe, tensorPairingL_coe, tensorPairingL_coe]
    -- both sides are continuous linear functionals on the algebraic tensor square agreeing on `tprod`
    have : (pairL Ψ).comp (PiTensorProduct.mapL (fun _ : Fin 2 => f)) = pairL (Ψ.bilinearComp f f) := by
      refine ContinuousLinearMap.coe_injective ?_
      refine PiTensorProduct.ext ?_
      refine MultilinearMap.ext fun m => ?_
      have e1 : (PiTensorProduct.tprod ℝ m : ⨂[ℝ] _ : Fin 2, Y) = tmulAlg (m 0) (m 1) :=
        (tmulAlg_eq_tprod m).symm
      simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply]
      rw [e1, PiTensorProduct.mapL_apply, tmulAlg, PiTensorProduct.map_tprod,
        show (PiTensorProduct.tprod ℝ fun i => (fun _ : Fin 2 => f.toLinearMap) i (![m 0, m 1] i) : ⨂[ℝ] _ : Fin 2, Y') =
          tmulAlg (f (m 0)) (f (m 1)) by
            unfold tmulAlg; congr 1; funext i; fin_cases i <;> rfl,
        pairL_tmulAlg]
      have h2 := pairL_tmulAlg (Ψ.bilinearComp f f) (m 0) (m 1)
      simp only [tmulAlg] at h2
      rw [h2]
      rfl
    exact congrArg (fun L => L x) this

end Tens2

end HRS.Uniform.Q45
