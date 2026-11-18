import HRS.Main.A34Aux19

/-!
# Packet A34, helper 20: `d_{C²}` of couplings and of convolutions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS

section SmoothDist

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

theorem a34_smoothDist_coupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X G : Ω → B) (hX : Measurable X) (hG : Measurable G)
    (hsub : Integrable (fun ω => ‖X ω - G ω‖) P) :
    smoothDist 2 (P.map X) (P.map G) ≤ ∫ ω, ‖X ω - G ω‖ ∂P := by
  have : Nonempty (CbUnitBall B 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (integral_nonneg fun ω => norm_nonneg _)
  have hΦc : Continuous Φ.1 := Φ.2.1.continuous
  have hΦ1 : Φ.1 ∈ CbUnitBall B 1 := cbUnitBall_mono Φ.2
  have hint : ∀ Y : Ω → B, Measurable Y → Integrable (fun ω => Φ.1 (Y ω)) P :=
    fun Y hY => Integrable.of_bound (hΦc.measurable.comp hY).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa using abs_apply_le_of_mem Φ.2 (Y ω))
  have e1 : ∫ z, Φ.1 z ∂(P.map X) = ∫ ω, Φ.1 (X ω) ∂P :=
    integral_map hX.aemeasurable hΦc.aestronglyMeasurable
  have e2 : ∫ z, Φ.1 z ∂(P.map G) = ∫ ω, Φ.1 (G ω) ∂P :=
    integral_map hG.aemeasurable hΦc.aestronglyMeasurable
  rw [e1, e2, ← integral_sub (hint X hX) (hint G hG)]
  calc |∫ ω, (Φ.1 (X ω) - Φ.1 (G ω)) ∂P|
      = ‖∫ ω, (Φ.1 (X ω) - Φ.1 (G ω)) ∂P‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖Φ.1 (X ω) - Φ.1 (G ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖X ω - G ω‖ ∂P :=
        integral_mono ((hint X hX).sub (hint G hG)).norm hsub
          (fun ω => norm_sub_le_of_mem_one hΦ1 _ _)

variable [SecondCountableTopology B]

theorem a34_int_conv (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 2) :
    ∫ z, Φ z ∂(μ ∗ ν) = ∫ y, ∫ x, Φ (x + y) ∂μ ∂ν := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hconv : μ ∗ ν = (μ.prod ν).map (fun p => p.1 + p.2) := rfl
  have hm : Measurable (fun p : B × B => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [hconv, integral_map hm.aemeasurable hΦc.aestronglyMeasurable]
  have hint : Integrable (fun p : B × B => Φ (p.1 + p.2)) (μ.prod ν) :=
    Integrable.of_bound (hΦc.measurable.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable 1
      (ae_of_all _ fun p => by simpa using abs_apply_le_of_mem hΦ (p.1 + p.2))
  rw [integral_prod_symm _ hint]

theorem a34_conv_left (μ₁ μ₂ ν : Measure B) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν] : smoothDist 2 (μ₁ ∗ ν) (μ₂ ∗ ν) ≤ smoothDist 2 μ₁ μ₂ := by
  have : Nonempty (CbUnitBall B 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (smoothDist_nonneg 2 μ₁ μ₂)
  rw [a34_int_conv μ₁ ν Φ.2, a34_int_conv μ₂ ν Φ.2]
  have hΦc : Continuous Φ.1 := Φ.2.1.continuous
  have hint : ∀ (μ : Measure B) [IsProbabilityMeasure μ], Integrable (fun y => ∫ x, Φ.1 (x + y) ∂μ) ν := by
    intro μ _
    refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun y => ?_)
    · have : Measurable fun p : B × B => Φ.1 (p.1 + p.2) :=
        hΦc.measurable.comp (measurable_fst.add measurable_snd)
      exact (this.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      calc |∫ x, Φ.1 (x + y) ∂μ| ≤ ∫ x, |Φ.1 (x + y)| ∂μ := by
            simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => Φ.1 (x + y))
        _ ≤ ∫ x, (1 : ℝ) ∂μ := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (integrable_const _) (ae_of_all _ fun x => abs_apply_le_of_mem Φ.2 _)
        _ = 1 := by simp
  rw [← integral_sub (hint μ₁) (hint μ₂)]
  calc |∫ y, (∫ x, Φ.1 (x + y) ∂μ₁ - ∫ x, Φ.1 (x + y) ∂μ₂) ∂ν|
      ≤ ∫ y, |∫ x, Φ.1 (x + y) ∂μ₁ - ∫ x, Φ.1 (x + y) ∂μ₂| ∂ν := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν)
          (fun y => ∫ x, Φ.1 (x + y) ∂μ₁ - ∫ x, Φ.1 (x + y) ∂μ₂)
    _ ≤ ∫ y, smoothDist 2 μ₁ μ₂ ∂ν := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun y => ?_)
        exact abs_integral_sub_le_smoothDist (cbUnitBall_translate Φ.2 y) μ₁ μ₂
    _ = smoothDist 2 μ₁ μ₂ := by simp

theorem a34_conv_right (μ ν₁ ν₂ : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] : smoothDist 2 (μ ∗ ν₁) (μ ∗ ν₂) ≤ smoothDist 2 ν₁ ν₂ := by
  rw [Measure.conv_comm μ ν₁, Measure.conv_comm μ ν₂]
  exact a34_conv_left ν₁ ν₂ μ

theorem a34_smoothDist_conv (μ₁ μ₂ ν₁ ν₂ : Measure B) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    smoothDist 2 (μ₁ ∗ ν₁) (μ₂ ∗ ν₂) ≤ smoothDist 2 μ₁ μ₂ + smoothDist 2 ν₁ ν₂ := by
  have : IsProbabilityMeasure (μ₂ ∗ ν₁) := inferInstance
  refine (smoothDist_triangle 2 (μ₁ ∗ ν₁) (μ₂ ∗ ν₁) (μ₂ ∗ ν₂)).trans ?_
  exact add_le_add (a34_conv_left μ₁ μ₂ ν₁) (a34_conv_right μ₂ ν₁ ν₂)

end SmoothDist

end HRS.A34
