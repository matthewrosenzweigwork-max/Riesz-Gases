import HRS.Uniform.Q45Sub4

/-!
# Lemma 3.20 `covariance_measure` (packet Q45), proved in the relocated form

`HRS/Uniform/Spec.lean` cannot import this file (the helper files `HRS/Uniform/Q45*.lean` import `Spec`), so the
statement is repeated verbatim as `covariance_measure_proof` and identified with the frozen statement by
`example := (@covariance_measure_proof : type_of% @covariance_measure)`.

Route: Jordan decomposition `D = D⁺ - D⁻` of the trace density (`Q45Jor*`), Gaussian martingales with covariance densities
`1_I D^±` (`Q45Gauss`), the stochastic convolution with a measurable version from Lemma 3.17 (`Q45Max`), the path tensors
`E[Z ⊗ Z]` in `𝒴 ⊗̂_π 𝒴` and their covariance formula (`Q45Cov*`, `Q45Ten*`), uniqueness through the separation of
points by terminal observations (`Q45Sep*`), assembly of the vector measure (`Q45Fam*`, `Q45VM`), and the reduction to the
separable closed span of the range of `j` (`Q45Trans*`, `Q45Sub*`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

/-- Lemma 3.20, proved. -/
theorem covariance_measure_proof (T K : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        (S : EvolData H E) (_ : S.MaxHyp T K),
      ∃ J : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T E)),
        (∀ D, IsTraceDensityL1 T D →
          (∀ I, MeasurableSet I → J D I = J D (I ∩ Set.Icc 0 T)) ∧
          (∀ I, MeasurableSet I → ∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ,
            tensorPairing Ψ (J D I) = tensorPairing Ψ.flip (J D I)) ∧
          (J D).variation (Set.Icc 0 T) ≤
            ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (D r)) ∧
          (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) (I : Set ℝ), MeasurableSet I →
            tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (J D I) =
              ∫ r in I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂),
                D r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) ∧
          ContinuousOn (fun t => J D (Set.Icc 0 t)) (Set.Icc 0 T)) ∧
        (∀ D D', IsTraceDensityL1 T D → IsTraceDensityL1 T D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
          J (fun r => a • D r + b • D' r) I = a • J D I + b • J D' I) := by
  rcases hT.eq_or_lt with h0 | hpos
  · -- `T = 0`: the zero measure
    subst h0
    refine ⟨0, le_rfl, ?_⟩
    intro H E _ _ _ _ _ _ _ _ _ S hS
    refine ⟨fun _ => 0, fun D hD => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro I hI; rfl
    · intro I hI Ψ; simp [HRS.Uniform.Q45.tensorPairing_eq]
    · simp [VectorMeasure.variation_zero]
    · intro t₁ t₂ ℓ₁ ℓ₂ I hI
      have hmin : (min (t₁ : ℝ) t₂) ≤ 0 := (min_le_left _ _).trans t₁.2.2
      have hz : volume (I ∩ Set.Icc (0 : ℝ) (min (t₁ : ℝ) t₂)) = 0 := by
        refine measure_mono_null Set.inter_subset_right ?_
        rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_eq_zero]
        exact hmin
      rw [setIntegral_measure_zero _ hz]
      simp [HRS.Uniform.Q45.tensorPairing_eq]
    · exact continuousOn_const
    · intro D D' hD hD' a b I hI; simp
  · obtain ⟨C, hC0, hC⟩ := HRS.Uniform.Q45.cov_transport T K hpos
    refine ⟨C, hC0, ?_⟩
    intro H E _ _ _ _ _ _ _ _ _ S hS
    obtain ⟨hev, h | h⟩ := hS
    · -- two levels: pass to the closed span of the range of `j`
      haveI : CompleteSpace (HRS.Uniform.Q45.E0 S) := (HRS.Uniform.Q45.E0_closed S).completeSpace_coe
      haveI : SecondCountableTopology (HRS.Uniform.Q45.E0 S) := by
        have hsep : TopologicalSpace.IsSeparable (HRS.Uniform.Q45.E0 S : Set E) := by
          have := (TopologicalSpace.isSeparable_range S.j.continuous).closure
          simpa [HRS.Uniform.Q45.E0, Submodule.topologicalClosure_coe, LinearMap.coe_range] using this
        haveI := hsep.separableSpace
        exact UniformSpace.secondCountable_of_separable _
      letI : MeasurableSpace (HRS.Uniform.Q45.E0 S) := borel _
      haveI : BorelSpace (HRS.Uniform.Q45.E0 S) := ⟨rfl⟩
      refine hC H E (HRS.Uniform.Q45.E0 S) S (HRS.Uniform.Q45.subData S)
        (HRS.Uniform.Q45.subData_maxHyp_twoLevel hpos hev h) (HRS.Uniform.Q45.E0 S).subtypeₗᵢ
        (fun x => rfl) (fun r t hr hrt htT y => ?_)
      exact HRS.Uniform.Q45.VE0_coe hev hr hrt htT y
    · -- one dissipative level: `j` is onto, so `E` itself is separable
      haveI : SecondCountableTopology E := by
        have hsep : TopologicalSpace.IsSeparable (Set.univ : Set E) := by
          have := TopologicalSpace.isSeparable_range S.j.continuous
          have hr : Set.range S.j = Set.univ := Set.range_eq_univ.2 h.2.1
          rwa [hr] at this
        haveI := TopologicalSpace.isSeparable_univ_iff.1 hsep
        exact UniformSpace.secondCountable_of_separable _
      letI : MeasurableSpace E := borel _
      haveI : BorelSpace E := ⟨rfl⟩
      exact hC H E E S S ⟨hev, Or.inr h⟩ (LinearIsometry.id) (fun x => rfl) (fun r t hr hrt htT y => rfl)

example := (@covariance_measure_proof : type_of% @covariance_measure)

end Uniform

end HRS
