import HRS.Sections.AdjKAAux7

/-!
# ADJKA part 8: images of Hilbert martingales under bounded operators, restriction to shorter horizons
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform

section Map

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- The image `L M` of a Hilbert martingale under a bounded operator `L : H → K` is a Hilbert martingale with
covariation `Σ(L^* ·, L^* ·)`. -/
theorem adjka_isHMC_map {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (L : H →L[ℝ] K) :
    IsHilbertMartingaleWithCovariation P ℱ T (fun τ ω => L (M τ ω))
      (fun σ ω => Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω)) where
  martingale := fun x => by
    have e : (fun τ ω => inner ℝ (L (M τ ω)) x) =
        fun τ ω => inner ℝ (M τ ω) (ContinuousLinearMap.adjoint L x) := by
      funext τ ω
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [e]
    exact hM.martingale _
  zero := by
    filter_upwards [hM.zero] with ω hω
    rw [hω, map_zero]
  cont := by
    filter_upwards [hM.cont] with ω hω
    exact L.continuous.comp_continuousOn hω
  sq_int := fun τ hτ => L.comp_memLp' (hM.sq_int τ hτ)
  sigma_meas := fun x y => hM.sigma_meas _ _
  sigma_adapted := fun σ x y => hM.sigma_adapted σ _ _
  sigma_traceClass := by
    filter_upwards [hM.sigma_traceClass] with ω hω σ hσ
    exact Kot.isTraceClassCov_formComp (hω σ hσ) _
  sigma_int := by
    have hsm : StronglyMeasurable fun ω => ∫ σ in Icc 0 T,
        traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω)) := by
      have hm := measurable_traceNormForm (H := K) (α := ℝ × Ω)
        (fun p => Kot.formComp (ContinuousLinearMap.adjoint L) (Sg p.1 p.2))
        (fun u v => hM.sigma_meas (ContinuousLinearMap.adjoint L u) (ContinuousLinearMap.adjoint L v))
      have := (hm.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
      exact this.integral_prod_right' (ν := volume.restrict (Icc 0 T))
    refine Integrable.mono' (hM.sigma_int.const_mul (‖L‖ ^ 2)) hsm.aestronglyMeasurable ?_
    filter_upwards [hM.sigma_traceClass, hM.sigma_pathint] with ω htc hpath
    have hb : ∀ σ ∈ Icc 0 T, traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω)) ≤
        ‖L‖ ^ 2 * traceNormForm (Sg σ ω) := fun σ hσ => by
      have := Kot.traceNormForm_formComp_le (htc σ hσ) (ContinuousLinearMap.adjoint L)
      rwa [ContinuousLinearMap.adjoint.norm_map L] at this
    have hint : IntegrableOn (fun σ => traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω)))
        (Icc 0 T) := by
      have hm := measurable_traceNormForm (H := K) (α := ℝ × Ω)
        (fun p => Kot.formComp (ContinuousLinearMap.adjoint L) (Sg p.1 p.2))
        (fun u v => hM.sigma_meas (ContinuousLinearMap.adjoint L u) (ContinuousLinearMap.adjoint L v))
      refine Integrable.mono' (hpath.const_mul (‖L‖ ^ 2)) ?_ ?_
      · exact (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
        rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
        exact hb σ hσ
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
    calc ∫ σ in Icc 0 T, traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω))
        ≤ ∫ σ in Icc 0 T, ‖L‖ ^ 2 * traceNormForm (Sg σ ω) :=
          setIntegral_mono_on hint (hpath.const_mul _) measurableSet_Icc hb
      _ = ‖L‖ ^ 2 * ∫ σ in Icc 0 T, traceNormForm (Sg σ ω) := integral_const_mul _ _
  sigma_pathint := by
    filter_upwards [hM.sigma_traceClass, hM.sigma_pathint] with ω htc hpath
    have hb : ∀ σ ∈ Icc 0 T, traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω)) ≤
        ‖L‖ ^ 2 * traceNormForm (Sg σ ω) := fun σ hσ => by
      have := Kot.traceNormForm_formComp_le (htc σ hσ) (ContinuousLinearMap.adjoint L)
      rwa [ContinuousLinearMap.adjoint.norm_map L] at this
    have hm := measurable_traceNormForm (H := K) (α := ℝ × Ω)
      (fun p => Kot.formComp (ContinuousLinearMap.adjoint L) (Sg p.1 p.2))
      (fun u v => hM.sigma_meas (ContinuousLinearMap.adjoint L u) (ContinuousLinearMap.adjoint L v))
    refine Integrable.mono' (hpath.const_mul (‖L‖ ^ 2)) ?_ ?_
    · exact (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
      rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
      exact hb σ hσ
  sigma_entry_int := by
    filter_upwards [hM.sigma_entry_int] with ω hω u v
    exact hω _ _
  covariation := fun x y => by
    have e : (fun τ ω => inner ℝ (L (M τ ω)) x * inner ℝ (L (M τ ω)) y -
        ∫ σ in Icc 0 τ, Kot.formComp (ContinuousLinearMap.adjoint L) (Sg σ ω) x y) =
        fun τ ω => inner ℝ (M τ ω) (ContinuousLinearMap.adjoint L x) *
          inner ℝ (M τ ω) (ContinuousLinearMap.adjoint L y) -
          ∫ σ in Icc 0 τ, Sg σ ω (ContinuousLinearMap.adjoint L x) (ContinuousLinearMap.adjoint L y) := by
      funext τ ω
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
      rfl
    rw [e]
    exact hM.covariation _ _

/-- Restriction to a shorter horizon. -/
theorem adjka_isHMC_mono {ℱ : Filtration ℝ mΩ} {T T' : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (hT' : T' ≤ T) : IsHilbertMartingaleWithCovariation P ℱ T' M Sg where
  martingale := hM.martingale
  zero := hM.zero
  cont := by
    filter_upwards [hM.cont] with ω hω
    exact hω.mono (Icc_subset_Icc_right hT')
  sq_int := fun τ hτ => hM.sq_int τ ⟨hτ.1, hτ.2.trans hT'⟩
  sigma_meas := hM.sigma_meas
  sigma_adapted := hM.sigma_adapted
  sigma_traceClass := by
    filter_upwards [hM.sigma_traceClass] with ω hω σ hσ
    exact hω σ ⟨hσ.1, hσ.2.trans hT'⟩
  sigma_int := by
    refine Integrable.mono' hM.sigma_int ?_ ?_
    · have hm := measurable_traceNormForm (H := H) (α := ℝ × Ω) (fun p => Sg p.1 p.2)
        (fun u v => hM.sigma_meas u v)
      have := (hm.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
      exact (this.integral_prod_right' (ν := volume.restrict (Icc 0 T'))).aestronglyMeasurable
    · filter_upwards [hM.sigma_pathint] with ω hω
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
      exact setIntegral_mono_set hω (Filter.Eventually.of_forall fun σ => traceNormForm_nonneg _)
        (Filter.Eventually.of_forall (Icc_subset_Icc_right hT'))
  sigma_pathint := by
    filter_upwards [hM.sigma_pathint] with ω hω
    exact hω.mono_set (Icc_subset_Icc_right hT')
  sigma_entry_int := by
    filter_upwards [hM.sigma_entry_int] with ω hω x y
    exact (hω x y).mono_set (Icc_subset_Icc_right hT')
  covariation := hM.covariation

end Map

end HRS.AdjK
