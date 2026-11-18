import HRS.MC.E213U16v
import HRS.MS.S21G2_M16

/-!
# S21G2 K06 -- independent heat-function pairings (R26-T3.K06)

If `Γ` is independent of `(Y, D, J)`, then `E[∂(heat Γ Φ)(Y)[D]] = E[∂Φ(Y + Γ)[D]]` and
`E[J(D²(heat Γ Φ)(Y))] = E[J(D²Φ(Y + Γ))]`.  Route: `heat Γ Φ = ∫ Φ(· + z) d(law Γ)` (merged generic derivative
formulas `u16_heat_fderiv`, `u16_heat_iter2`), a product-measure Fubini lemma for independent pairs, and separability of
`projTensor B 2` (so the product σ-algebra on `B × B × projTensor B 2` is Borel).  Contract verbatim; helpers `s21g2_k06_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_k06_sc {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [SecondCountableTopology B]
    (k : ℕ) : SecondCountableTopology (HRS.projTensor B k) := by
  have h1 : TopologicalSpace.IsSeparable (Set.range (HRS.elemTensor (B := B) (k := k))) :=
    TopologicalSpace.isSeparable_range (HRS.MC.E213T.e213t_continuous_elemTensor k)
  have h2 := (h1.span (R := ℝ)).closure
  have h3 : TopologicalSpace.IsSeparable ((HRS.projTensor B k : Submodule ℝ (HRS.TensorDual B k)) :
      Set (HRS.TensorDual B k)) := by
    simpa [HRS.projTensor, Submodule.topologicalClosure_coe] using h2
  haveI := h3.separableSpace
  exact UniformSpace.secondCountable_of_separable _

/-- Independence turns `E G(A, Γ)` into the iterated integral over the law of `Γ`. -/
theorem s21g2_k06_fubini {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α B : Type*} [MeasurableSpace α] [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B] {A : Ω → α} {Γ : Ω → B} (hind : IndepFun Γ A P)
    (hA : AEMeasurable A P) (hΓ : AEMeasurable Γ P) {G : α × B → ℝ} (hG : Measurable G)
    (hint : Integrable (fun ω => G (A ω, Γ ω)) P) :
    ∫ ω, G (A ω, Γ ω) ∂P = ∫ ω, ∫ z, G (A ω, z) ∂(P.map Γ) ∂P := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hΓ hA).1 hind
  have hm : Measurable (fun p : B × α => G (p.2, p.1)) := hG.comp (measurable_snd.prodMk measurable_fst)
  have hmap : AEMeasurable (fun ω => (Γ ω, A ω)) P := hΓ.prodMk hA
  have hi' : Integrable (fun p : B × α => G (p.2, p.1)) ((P.map Γ).prod (P.map A)) := by
    rw [← hprod]
    exact (integrable_map_measure hm.aestronglyMeasurable hmap).2 hint
  have e1 : ∫ ω, G (A ω, Γ ω) ∂P = ∫ p : B × α, G (p.2, p.1) ∂((P.map Γ).prod (P.map A)) := by
    rw [← hprod, integral_map hmap hm.aestronglyMeasurable]
  rw [e1, integral_prod_symm _ hi']
  have hmeas : AEStronglyMeasurable (fun a : α => ∫ z, G (a, z) ∂(P.map Γ)) (P.map A) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := P.map Γ)).aestronglyMeasurable
  rw [← integral_map hA hmeas]

theorem r26t3_independent_heat_pairings {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ Y D : Ω → B) (J : Ω → HRS.projTensor B 2)
    (hmΓ : AEStronglyMeasurable Γ P) (hmY : AEStronglyMeasurable Y P)
    (hmD : AEStronglyMeasurable D P) (hmJ : AEStronglyMeasurable J P)
    (hind : IndepFun Γ (fun ω => (Y ω,D ω,J ω)) P)
    (hD : Integrable D P) (hJ : Integrable J P) (Φ : B → ℝ) (hΦ : HRS.MemCb 5 Φ) :
    (∫ ω, fderiv ℝ (r26t3_heat P Γ Φ) (Y ω) (D ω) ∂P)=
      ∫ ω, fderiv ℝ Φ (Y ω+Γ ω) (D ω) ∂P ∧
    (∫ ω, (J ω : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 (r26t3_heat P Γ Φ) (Y ω)) ∂P)=
      ∫ ω, (J ω : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Y ω+Γ ω)) ∂P := by
  haveI := s21g2_k06_sc (B := B) 2
  have hΓm : AEMeasurable Γ P := hmΓ.aemeasurable
  haveI : IsProbabilityMeasure (P.map Γ) := (Measure.isProbabilityMeasure_map_iff hΓm).2 inferInstance
  have hA' : AEStronglyMeasurable (fun ω => (Y ω, D ω, J ω)) P := hmY.prodMk (hmD.prodMk hmJ)
  have hA : AEMeasurable (fun ω => (Y ω, D ω, J ω)) P := hA'.aemeasurable
  have hheat : r26t3_heat P Γ Φ = fun y => ∫ z, Φ (y + (ContinuousLinearMap.id ℝ B) z) ∂(P.map Γ) := by
    funext y
    exact (integral_map (f := fun z => Φ (y + z)) hΓm
      (hΦ.1.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable).symm
  have hAΓ : AEStronglyMeasurable (fun ω => ((Y ω, D ω, J ω), Γ ω)) P := hA'.prodMk hmΓ
  have hC1 : Continuous fun p : (B × B × HRS.projTensor B 2) × B => fderiv ℝ Φ (p.1.1 + p.2) p.1.2.1 :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B) (F := ℝ)).continuous.comp
      (((hΦ.1.continuous_fderiv (by norm_num)).comp
        ((continuous_fst.comp continuous_fst).add continuous_snd)).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_fst)))
  have hC2 : Continuous fun p : (B × B × HRS.projTensor B 2) × B =>
      (p.1.2.2 : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (p.1.1 + p.2)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B [×2]→L[ℝ] ℝ) (F := ℝ)).continuous.comp
      (((continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_fst)))).prodMk
        ((hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp
          ((continuous_fst.comp continuous_fst).add continuous_snd)))
  refine ⟨?_, ?_⟩
  · have hint : Integrable (fun ω => fderiv ℝ Φ (Y ω + Γ ω) (D ω)) P := by
      refine (hD.norm.const_mul (cbNorm 5 Φ)).mono'
        (hC1.comp_aestronglyMeasurable hAΓ) (ae_of_all _ fun ω => ?_)
      calc ‖fderiv ℝ Φ (Y ω + Γ ω) (D ω)‖ ≤ ‖fderiv ℝ Φ (Y ω + Γ ω)‖ * ‖D ω‖ :=
            (fderiv ℝ Φ _).le_opNorm _
        _ ≤ cbNorm 5 Φ * ‖D ω‖ := by
            gcongr; exact HRS.MC.E213U16.u16_norm_fderiv_le hΦ _
    have := s21g2_k06_fubini hind hA hΓm (G := fun p => fderiv ℝ Φ (p.1.1 + p.2) p.1.2.1)
      hC1.measurable hint
    rw [this]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    rw [hheat]
    exact HRS.MC.E213U16.u16_heat_fderiv (P.map Γ) (ContinuousLinearMap.id ℝ B) hΦ (Y ω) (D ω)
  · have hint : Integrable (fun ω => (J ω : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Y ω + Γ ω))) P := by
      refine (hJ.norm.mul_const (cbNorm 5 Φ)).mono'
        (hC2.comp_aestronglyMeasurable hAΓ) (ae_of_all _ fun ω => ?_)
      calc ‖(J ω : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Y ω + Γ ω))‖
          ≤ ‖(J ω : HRS.TensorDual B 2)‖ * ‖iteratedFDeriv ℝ 2 Φ (Y ω + Γ ω)‖ :=
            (J ω : HRS.TensorDual B 2).le_opNorm _
        _ ≤ ‖J ω‖ * cbNorm 5 Φ :=
            mul_le_mul (le_of_eq rfl) (HRS.MC.E213U16.u16_norm_iter2_le hΦ _) (norm_nonneg _)
              (norm_nonneg _)
    have := s21g2_k06_fubini hind hA hΓm
      (G := fun p => (p.1.2.2 : HRS.TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (p.1.1 + p.2)))
      hC2.measurable hint
    rw [this]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    rw [hheat]
    exact HRS.MC.E213U16.u16_heat_iter2 (P.map Γ) (ContinuousLinearMap.id ℝ B) hΦ (Y ω) (J ω : HRS.TensorDual B 2)

end HRS.MS.R26T3
