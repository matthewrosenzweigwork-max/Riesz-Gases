import HRS.MC.E213TElem

/-!
# S11.1 I12: cubic projective tensor for an arbitrary measure

Unlike the existing probability-measure interface, this proof integrates
directly in the closed submodule. No normalization of P is required.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 5
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.MC.E213T

theorem r26t6c_cubic_tensor_expectation {B Omega : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Omega] (P : Measure Omega)
    (L : Omega → B) (hL : MemLp L 3 P) :
    ∃ I : projTensor B 3,
      (∀ M : B [×3]→L[ℝ] ℝ,
        (I : TensorDual B 3) M = ∫ w, M ![L w,L w,L w] ∂P) ∧
      ‖I‖ ≤ ∫ w, ‖L w‖ ^ 3 ∂P := by
  let S : Submodule ℝ (TensorDual B 3) := projTensor B 3
  let F : Omega → S := fun ω =>
    ⟨elemTensor ![L ω, L ω, L ω], elemTensor3_mem _ _ _⟩
  have hcont : Continuous (fun x : B =>
      (⟨elemTensor ![x, x, x], elemTensor3_mem x x x⟩ : S)) := by
    refine Continuous.subtype_mk ?_ _
    exact elemTensor3_continuous.comp
      (continuous_id.prodMk (continuous_id.prodMk continuous_id))
  have hFm : AEStronglyMeasurable F P :=
    hcont.comp_aestronglyMeasurable hL.aestronglyMeasurable
  have hnorm : ∀ ω, ‖F ω‖ ≤ ‖L ω‖ ^ 3 := by
    intro ω
    have hb := elemTensor3_norm_le (L ω) (L ω) (L ω)
    change ‖(elemTensor ![L ω, L ω, L ω] : TensorDual B 3)‖ ≤ ‖L ω‖ ^ 3
    convert hb using 1
    ring
  have h3 : Integrable (fun ω => ‖L ω‖ ^ 3) P :=
    hL.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  have hFi : Integrable F P :=
    Integrable.mono' h3 hFm (ae_of_all _ hnorm)
  letI : IsClosed (S : Set (TensorDual B 3)) :=
    Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace S := inferInstance
  let I : S := ∫ ω, F ω ∂P
  have hcoe : (I : TensorDual B 3) =
      ∫ ω, (F ω : TensorDual B 3) ∂P := by
    exact ((S.subtypeL).integral_comp_comm hFi).symm
  have hnormI : ‖I‖ ≤ ∫ ω, ‖L ω‖ ^ 3 ∂P := by
    calc
      _ ≤ ∫ ω, ‖F ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖L ω‖ ^ 3 ∂P :=
        integral_mono hFi.norm h3 hnorm
  refine ⟨I, ?_, hnormI⟩
  intro M
  rw [hcoe]
  have hint : Integrable (fun ω => (F ω : TensorDual B 3)) P :=
    S.subtypeL.integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hint]
  apply integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [F, elemTensor_apply]

end HRS.MS.R26T6C
