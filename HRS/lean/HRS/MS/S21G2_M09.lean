import HRS.MC.E213TElem

/-!
# S21G2 M09 -- projective second-moment tensor `E[X ⊗ Y]` (R26-T3.M09)

For `X, Y ∈ L²(P; B)` (strongly measurable) the Bochner integral of the elementary tensor `X ⊗ Y` lies in
`projTensor B 2`, has norm `≤ ‖X‖_{L²} ‖Y‖_{L²}`, and evaluates on every bounded bilinear form `M` as
`E M(X, Y)`.  The contract is taken verbatim.  Helper names carry the prefix `s21g2_m09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

set_option maxSynthPendingDepth 3

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HRS.MS.R26T3

theorem r26t3_aux_tensor {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → B) (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (h2 : MemLp X 2 P ∧ MemLp Y 2 P) :
    ∃ J : projTensor B 2, (J : TensorDual B 2)=∫ ω, elemTensor ![X ω,Y ω] ∂P ∧
      ‖J‖≤Real.sqrt (∫ ω, ‖X ω‖^2 ∂P)*Real.sqrt (∫ ω, ‖Y ω‖^2 ∂P) ∧
      ∀ M : B [×2]→L[ℝ] ℝ, (J : TensorDual B 2) M=∫ ω, M ![X ω,Y ω] ∂P := by
  have hcont : Continuous fun p : B × B => (elemTensor ![p.1, p.2] : TensorDual B 2) := by
    refine (HRS.MC.E213T.e213t_continuous_elemTensor 2).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hmeas : AEStronglyMeasurable (fun ω => (elemTensor ![X ω, Y ω] : TensorDual B 2)) P :=
    hcont.comp_aestronglyMeasurable (hX.prodMk hY)
  have hnorm : ∀ ω, ‖(elemTensor ![X ω, Y ω] : TensorDual B 2)‖ ≤ ‖X ω‖ * ‖Y ω‖ := fun ω => by
    simpa [Fin.prod_univ_two] using HRS.MC.E213T.e213t_norm_elemTensor_le (![X ω, Y ω] : Fin 2 → B)
  have hXY : Integrable (fun ω => ‖X ω‖ * ‖Y ω‖) P := h2.1.norm.integrable_mul h2.2.norm
  have hint : Integrable (fun ω => (elemTensor ![X ω, Y ω] : TensorDual B 2)) P :=
    Integrable.mono' hXY hmeas (ae_of_all _ hnorm)
  have hmem : (∫ ω, (elemTensor ![X ω, Y ω] : TensorDual B 2) ∂P) ∈ projTensor B 2 :=
    HRS.MC.E213T.e213t_integral_mem _ (Submodule.isClosed_topologicalClosure _) hint
      (ae_of_all _ fun ω => HRS.MC.E213T.elemTensor_mem_projTensor _)
  refine ⟨⟨_, hmem⟩, rfl, ?_, fun M => ?_⟩
  · show ‖∫ ω, (elemTensor ![X ω, Y ω] : TensorDual B 2) ∂P‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ((integral_mono hint.norm hXY hnorm).trans ?_)
    have := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => norm_nonneg (X ω)) (ae_of_all _ fun ω => norm_nonneg (Y ω))
      (by simpa using h2.1.norm) (by simpa using h2.2.norm)
    simpa [Real.sqrt_eq_rpow, Real.rpow_two] using this
  · show (∫ ω, (elemTensor ![X ω, Y ω] : TensorDual B 2) ∂P) M = _
    rw [ContinuousLinearMap.integral_apply hint]
    simp only [elemTensor_apply]

end HRS.MS.R26T3
