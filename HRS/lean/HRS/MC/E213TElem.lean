import HRS.Prob.Gaussian

/-!
# Packet e213c, file 1: elementary tensors and Bochner integrals of triple products

Generic interface (`B` a real normed space, `P` a probability measure) for Theorem 2.13:
`elemTensor` is a bounded multilinear map, `bochTensor3 P x y z = ∫ elemTensor ![x ω, y ω, z ω] ∂P`
lies in `projTensor B 3`, has the evaluation formula and the norm bound `≤ ∫ ‖x‖‖y‖‖z‖`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E213T

open HRS

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The elementary-tensor map as a continuous multilinear map `B [×k]→L TensorDual B k`. -/
def elemTensorCMM (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => B) (TensorDual B k) :=
  ContinuousLinearMap.flipMultilinear
    (ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => B) ℝ))

@[simp] theorem elemTensorCMM_apply {k : ℕ} (v : Fin k → B) :
    elemTensorCMM B k v = elemTensor v := by
  ext M
  simp [elemTensorCMM, elemTensor]

/-- `elemTensor` is continuous (indeed multilinear and bounded). -/
theorem e213t_continuous_elemTensor (k : ℕ) :
    Continuous fun v : Fin k → B => (elemTensor v : TensorDual B k) := by
  have h : (fun v : Fin k → B => (elemTensor v : TensorDual B k)) = elemTensorCMM B k := by
    funext v; simp
  rw [h]
  exact (elemTensorCMM B k).cont

/-- Norm bound `‖x₁ ⊗ ⋯ ⊗ x_k‖ ≤ ∏ ‖xᵢ‖` for elementary tensors. -/
theorem e213t_norm_elemTensor_le {k : ℕ} (v : Fin k → B) :
    ‖(elemTensor v : TensorDual B k)‖ ≤ ∏ i, ‖v i‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
  rw [elemTensor_apply]
  calc ‖M v‖ ≤ ‖M‖ * ∏ i, ‖v i‖ := M.le_opNorm _
    _ = (∏ i, ‖v i‖) * ‖M‖ := mul_comm _ _

/-- (1) `‖elemTensor ![x,y,z]‖ ≤ ‖x‖ * ‖y‖ * ‖z‖`. -/
theorem elemTensor3_norm_le (x y z : B) :
    ‖(elemTensor ![x, y, z] : TensorDual B 3)‖ ≤ ‖x‖ * ‖y‖ * ‖z‖ := by
  have := e213t_norm_elemTensor_le (![x, y, z] : Fin 3 → B)
  simpa [Fin.prod_univ_three] using this

/-- The map `(x,y,z) ↦ elemTensor ![x,y,z]` is continuous `B × B × B → TensorDual B 3`. -/
theorem elemTensor3_continuous :
    Continuous fun p : B × B × B => (elemTensor ![p.1, p.2.1, p.2.2] : TensorDual B 3) := by
  refine (e213t_continuous_elemTensor 3).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

/-- Every elementary tensor lies in `projTensor B k`. -/
theorem elemTensor_mem_projTensor {k : ℕ} (v : Fin k → B) :
    (elemTensor v : TensorDual B k) ∈ projTensor B k :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)

/-- (1) `elemTensor ![x,y,z] ∈ projTensor B 3`. -/
theorem elemTensor3_mem (x y z : B) :
    (elemTensor ![x, y, z] : TensorDual B 3) ∈ projTensor B 3 :=
  elemTensor_mem_projTensor _

/-- A continuous linear map `TensorDual E k →L TensorDual B k'` sending every elementary tensor into
`projTensor B k'` sends `projTensor E k` into `projTensor B k'` (continuity and closedness). -/
theorem e213t_map_projTensor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k k' : ℕ}
    (T : TensorDual E k →L[ℝ] TensorDual B k')
    (hT : ∀ v : Fin k → E, T (elemTensor v) ∈ projTensor B k') :
    ∀ u ∈ projTensor E k, T u ∈ projTensor B k' := by
  have hcl : IsClosed ((projTensor B k').comap (T : TensorDual E k →ₗ[ℝ] TensorDual B k') :
      Set (TensorDual E k)) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hle : projTensor E k ≤ (projTensor B k').comap (T : TensorDual E k →ₗ[ℝ] TensorDual B k') := by
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hT v
  exact fun u hu => hle hu

section Bochner

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An integrable function with values (a.e.) in a closed submodule has its integral there. -/
theorem e213t_integral_mem {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F)) {f : Ω → F} (hf : Integrable f P)
    (hmem : ∀ᵐ ω ∂P, f ω ∈ S) : ∫ ω, f ω ∂P ∈ S := by
  have := Convex.average_mem S.convex hS hmem hf
  simpa [average_eq_integral] using this

variable (P) in
/-- (2) The Bochner tensor `E[x ⊗ y ⊗ z] ∈ TensorDual B 3`, `∫ ω, elemTensor ![x ω, y ω, z ω] ∂P`. -/
def bochTensor3 (x y z : Ω → B) : TensorDual B 3 :=
  ∫ ω, (elemTensor ![x ω, y ω, z ω] : TensorDual B 3) ∂P

/-- (2) The integrand of `bochTensor3` is a.e. strongly measurable. -/
theorem bochTensor3_aestronglyMeasurable {x y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P) :
    AEStronglyMeasurable (fun ω => (elemTensor ![x ω, y ω, z ω] : TensorDual B 3)) P :=
  elemTensor3_continuous.comp_aestronglyMeasurable (hx.prodMk (hy.prodMk hz))

/-- (2) Integrability of the integrand of `bochTensor3` when `‖x‖‖y‖‖z‖` is integrable. -/
theorem bochTensor3_integrable {x y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hint : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    Integrable (fun ω => (elemTensor ![x ω, y ω, z ω] : TensorDual B 3)) P :=
  Integrable.mono' hint (bochTensor3_aestronglyMeasurable hx hy hz)
    (ae_of_all _ fun ω => elemTensor3_norm_le _ _ _)

/-- (2) `bochTensor3 P x y z ∈ projTensor B 3`. -/
theorem bochTensor3_mem {x y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hint : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    bochTensor3 P x y z ∈ projTensor B 3 :=
  e213t_integral_mem _ (Submodule.isClosed_topologicalClosure _)
    (bochTensor3_integrable hx hy hz hint) (ae_of_all _ fun ω => elemTensor3_mem _ _ _)

/-- (2) Evaluation formula: `bochTensor3 P x y z M = ∫ M ![x ω, y ω, z ω] ∂P`. -/
theorem bochTensor3_apply {x y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hint : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P) (M : B [×3]→L[ℝ] ℝ) :
    bochTensor3 P x y z M = ∫ ω, M ![x ω, y ω, z ω] ∂P := by
  unfold bochTensor3
  rw [ContinuousLinearMap.integral_apply (bochTensor3_integrable hx hy hz hint)]
  simp only [elemTensor_apply]

/-- (2) Norm bound: `‖bochTensor3 P x y z‖ ≤ ∫ ‖x‖‖y‖‖z‖`. -/
theorem norm_bochTensor3_le {x y z : Ω → B} (hx : AEStronglyMeasurable x P)
    (hy : AEStronglyMeasurable y P) (hz : AEStronglyMeasurable z P)
    (hint : Integrable (fun ω => ‖x ω‖ * ‖y ω‖ * ‖z ω‖) P) :
    ‖bochTensor3 P x y z‖ ≤ ∫ ω, ‖x ω‖ * ‖y ω‖ * ‖z ω‖ ∂P := by
  unfold bochTensor3
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono (bochTensor3_integrable hx hy hz hint).norm hint
    fun ω => elemTensor3_norm_le _ _ _

end Bochner

end HRS.MC.E213T
end
