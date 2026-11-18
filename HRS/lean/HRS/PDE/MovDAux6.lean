import HRS.PDE.MovDAux5
import HRS.Appendix.B15BAux1

/-!
# MOVD Aux6: abstract form of `movT_source_limit_cond`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

theorem movd_limit_cond_abstract {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} {Z Zt : ℝ → Ω → α} (hZ : ∀ r, Measurable (Z r))
    (hZt : ∀ r, Zt r =ᵐ[P] Z r) (hZtm : Measurable (Function.uncurry Zt))
    {Q : ℝ → Measure α} (hQ : ∀ r ∈ Set.Icc 0 T, IsProbabilityMeasure (Q r))
    {Φ : ℝ → α → ℝ} {Ψ : ℝ × α → ℝ} (hΨ : Measurable Ψ)
    (hΨeq : ∀ r ∈ Set.Icc 0 T, ∀ᵐ ω ∂P, Ψ (r, Z r ω) = Φ r (Z r ω))
    (hΦQ : ∀ r ∈ Set.Icc 0 T, AEMeasurable (Φ r) (Q r))
    {A : ℕ → Set Ω} (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ r ∈ Set.Icc 0 T,
      ∫⁻ x, ENNReal.ofReal (Real.exp (l * |Φ r x|)) ∂(Q r) ≤ ENNReal.ofReal (Real.exp C))
    (hH : ∃ C : ℝ, ∀ k, ∀ r ∈ Set.Icc 0 T,
      relEntropy ((movT_cond P (A k)).map (Z r)) (Q r) ≤ ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (Φ r) (P.map (Z r))) ∧
    IntegrableOn (fun r => ∫ x, Φ r x ∂(P.map (Z r))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun k => ∫ r in Set.Icc 0 t, ∫ x, Φ r x ∂((movT_cond P (A k)).map (Z r))) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ x, Φ r x ∂(P.map (Z r)))) := by
  obtain ⟨l, C, hl, hexpQ⟩ := hexp
  obtain ⟨C', hH⟩ := hH
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → P (A k) ≠ 0 := by
    obtain ⟨k₀, hk⟩ := eventually_atTop.1 (hP.eventually (lt_mem_nhds (zero_lt_one' ℝ≥0∞)))
    exact ⟨k₀, fun k hk' => (hk k hk').ne'⟩
  have hPk : ∀ k, k₀ ≤ k → IsProbabilityMeasure (movT_cond P (A k)) := fun k hk =>
    movT_cond_isProb P (hk₀ k hk) (measure_ne_top _ _)
  have hfk : ∀ k, k₀ ≤ k → ∀ r, IsProbabilityMeasure ((movT_cond P (A k)).map (Z r)) := by
    intro k hk r
    have := hPk k hk
    infer_instance
  have hfP : ∀ r, IsProbabilityMeasure (P.map (Z r)) := fun r => inferInstance
  -- lower semicontinuity of the entropy
  have hlsc : ∀ r ∈ Set.Icc 0 T, relEntropy (P.map (Z r)) (Q r) ≤ ENNReal.ofReal C' := by
    intro r hr
    have := hQ r hr
    have := hfP r
    have : ∀ n : ℕ, IsProbabilityMeasure ((movT_cond P (A (n + k₀))).map (Z r)) := fun n =>
      hfk _ (by omega) r
    have hn := b15b_klDiv_liminf_le (P := P.map (Z r)) (Q := Q r)
      (Pn := fun n : ℕ => (movT_cond P (A (n + k₀))).map (Z r)) (Qn := fun _ => Q r)
      (fun φ hφ => by
        obtain ⟨Cφ, hCφ⟩ := (isCompact_univ (X := α)).exists_bound_of_continuousOn hφ.continuousOn
        exact movd_cond_narrow P (hZ r) (A := fun n => A (n + k₀)) (fun n => hA _)
          (hP.comp (tendsto_add_atTop_nat k₀)) hφ ⟨Cφ, fun x => by
            simpa using hCφ x (Set.mem_univ x)⟩)
      (fun φ _ => tendsto_const_nhds)
    refine hn.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    exact hH (n + k₀) r hr
  -- entropy inequality
  have hKey : ∀ r ∈ Set.Icc 0 T, ∀ ν : Measure α, IsProbabilityMeasure ν →
      klDiv ν (Q r) ≤ ENNReal.ofReal C' →
      ν ≪ Q r ∧ Integrable (Φ r) ν ∧ ∫ x, |Φ r x| ∂ν ≤ (max C' 0 + C) / l := by
    intro r hr ν _ hνH
    have := hQ r hr
    have hne : klDiv ν (Q r) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hνH
    have hac : ν ≪ Q r := (klDiv_ne_top_iff.1 hne).1
    obtain ⟨hi, hb⟩ := movspec_int_le ν (Q r) ((hΦQ r hr).mono_ac hac) (hΦQ r hr) hl (hexpQ r hr) hne
    refine ⟨hac, hi, hb.trans ?_⟩
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hνH
    rw [ENNReal.toReal_ofReal'] at h1
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  -- measurability in `r`
  have hmeasG : ∀ μ : Measure Ω, SFinite μ → μ ≪ P → (∀ r ∈ Set.Icc 0 T, μ.map (Z r) ≪ Q r) →
      (Measurable fun r : ℝ => ∫ ω, Ψ (r, Zt r ω) ∂μ) ∧
      ∀ r ∈ Set.Icc 0 T, ∫ x, Φ r x ∂(μ.map (Z r)) = ∫ ω, Ψ (r, Zt r ω) ∂μ := by
    intro μ _ hμ hμQ
    refine ⟨?_, fun r hr => ?_⟩
    · have : Measurable fun p : ℝ × Ω => Ψ (p.1, Zt p.1 p.2) := hΨ.comp (measurable_fst.prodMk hZtm)
      exact (this.stronglyMeasurable.integral_prod_right').measurable
    · rw [integral_map (hZ r).aemeasurable ((hΦQ r hr).mono_ac (hμQ r hr)).aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [hμ.ae_le (hΨeq r hr), hμ.ae_le (hZt r)] with ω h1 h2
      show Φ r (Z r ω) = Ψ (r, Zt r ω)
      rw [h2, h1]
  set B : ℝ := (max C' 0 + C) / l with hB
  have hKP : ∀ r ∈ Set.Icc 0 T, P.map (Z r) ≪ Q r ∧ Integrable (Φ r) (P.map (Z r)) ∧
      ∫ x, |Φ r x| ∂(P.map (Z r)) ≤ B := fun r hr =>
    have := hfP r
    hKey r hr _ inferInstance (hlsc r hr)
  have hPm := hmeasG P inferInstance (Measure.AbsolutelyContinuous.refl P) (fun r hr => (hKP r hr).1)
  refine ⟨fun r hr => (hKP r hr).2.1, ?_, ?_⟩
  · -- integrability of `r ↦ ∫ Φ_r df_r`
    refine Integrable.of_bound (C := B) ?_ ?_
    · refine (hPm.1.aestronglyMeasurable (μ := volume.restrict (Set.Icc 0 T))).congr ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => (hPm.2 r hr).symm)
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      have := hfP r
      calc ‖∫ x, Φ r x ∂(P.map (Z r))‖ ≤ ∫ x, ‖Φ r x‖ ∂(P.map (Z r)) := norm_integral_le_integral_norm _
        _ ≤ B := (hKP r hr).2.2
  · intro t ht
    have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · refine eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩
      have := hPk k hk
      have hack : ∀ r ∈ Set.Icc 0 T, (movT_cond P (A k)).map (Z r) ≪ Q r := fun r hr =>
        have := hfk k hk r
        (hKey r hr _ inferInstance (hH k r hr)).1
      have hm := hmeasG (movT_cond P (A k)) inferInstance (movd_cond_ac P (A k)) hack
      refine (hm.1.aestronglyMeasurable (μ := volume.restrict (Set.Icc 0 t))).congr ?_
      exact (ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun r hr => (hm.2 r (hsub hr)).symm)
    · refine eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      have := hPk k hk
      have := hfk k hk r
      have := hKey r (hsub hr) _ inferInstance (hH k r (hsub hr))
      calc ‖∫ x, Φ r x ∂((movT_cond P (A k)).map (Z r))‖
          ≤ ∫ x, ‖Φ r x‖ ∂((movT_cond P (A k)).map (Z r)) := norm_integral_le_integral_norm _
        _ ≤ B := this.2.2
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      exact movd_cond_tendsto_integral P (hZ r) hA hP (hKP r (hsub hr)).2.1

end HRS

end
