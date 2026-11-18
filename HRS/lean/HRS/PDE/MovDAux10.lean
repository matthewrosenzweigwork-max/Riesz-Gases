import HRS.PDE.MovDAux9

/-!
# MOVD Aux10: abstract form of `movT_source_limit_bdd` (Hölder uniform integrability + dominated convergence in time)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

theorem movd_abs_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hm : AEStronglyMeasurable h μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ ω, ‖h ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) : ‖∫ ω, h ω ∂μ‖ ≤ 1 + B := by
  have h1 : ∫⁻ ω, ‖h ω‖ₑ ∂μ ≤ ENNReal.ofReal (1 + B) := by
    calc ∫⁻ ω, ‖h ω‖ₑ ∂μ ≤ ∫⁻ ω, (1 + ‖h ω‖ₑ ^ 2) ∂μ := by
          refine lintegral_mono fun ω => ?_
          set a : ℝ≥0∞ := ‖h ω‖ₑ
          rcases le_total a 1 with ha | ha
          · exact ha.trans le_self_add
          · calc a = a * 1 := (mul_one a).symm
              _ ≤ a * a := by gcongr
              _ = a ^ 2 := (sq a).symm
              _ ≤ 1 + a ^ 2 := le_add_self
      _ = 1 + ∫⁻ ω, ‖h ω‖ₑ ^ 2 ∂μ := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ 1 + ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (1 + B) := by
          rw [ENNReal.ofReal_add zero_le_one hB0, ENNReal.ofReal_one]
  have h2 := norm_integral_le_lintegral_norm (μ := μ) h
  simp only [ofReal_norm] at h2
  have h3 : (∫⁻ ω, ‖h ω‖ₑ ∂μ).toReal ≤ 1 + B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  exact h2.trans h3

theorem movd_limit_bdd_abstract {α : Type*} [MeasurableSpace α] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
    {Zn : ℕ → ℝ → Ω → α} {Z : ℝ → Ω → α} (hZn : ∀ n r, Measurable (Zn n r))
    (hZ : ∀ r, Measurable (Z r))
    {Qn : ℕ → ℝ → Measure α} (hQn : ∀ n, ∀ r ∈ Set.Icc 0 T, IsFiniteMeasure (Qn n r))
    {Sn : ℕ → ℝ → α → ℝ} {R : ℝ → α → ℝ}
    (hSm : ∀ n, ∀ r ∈ Set.Icc 0 T, Measurable (Sn n r))
    (hR : ∀ r ∈ Set.Icc 0 T, AEStronglyMeasurable (R r) (P.map (Z r)))
    (hpt : ∀ r ∈ Set.Icc 0 T,
      ∀ᵐ ω ∂P, Tendsto (fun n => Sn n r (Zn n r ω)) atTop (𝓝 (R r (Z r ω))))
    (hGc : ∀ n, ContinuousOn (fun r => ∫ z, Sn n r z ∂(P.map (Zn n r))) (Set.Icc 0 T))
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ z, ENNReal.ofReal (Real.exp (l * |Sn n r z|)) ∂(Qn n r) ≤ ENNReal.ofReal (Real.exp C))
    (hLq : ∃ q C : ℝ, 1 < q ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      P.map (Zn n r) ≪ Qn n r ∧
      eLpNorm ((P.map (Zn n r)).rnDeriv (Qn n r)) (ENNReal.ofReal q) (Qn n r) ≤ ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (R r) (P.map (Z r))) ∧
    IntegrableOn (fun r => ∫ z, R r z ∂(P.map (Z r))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => ∫ r in Set.Icc 0 t, ∫ z, Sn n r z ∂(P.map (Zn n r))) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ z, R r z ∂(P.map (Z r)))) := by
  obtain ⟨l, C, hl, hexpQ⟩ := hexp
  obtain ⟨q, Cq, hq, hLq'⟩ := hLq
  set B : ℝ := movd_Bhold q (max Cq 0) l C with hB
  have hB0 : 0 ≤ B := by
    rw [hB, movd_Bhold]
    have : 0 ≤ (1 + (⌈2 * (q / (q - 1))⌉₊.factorial : ℝ)) / l ^ (2 * (q / (q - 1))) * Real.exp C := by
      positivity
    exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg this _)
  -- the `L²` bound
  have hL2 : ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ ω, ‖Sn n r (Zn n r ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal B := by
    filter_upwards [hexpQ, hLq'] with n h1 h2 r hr
    have : IsFiniteMeasure (Qn n r) := hQn n r hr
    obtain ⟨hac, hnorm⟩ := h2 r hr
    have hmeas : Measurable fun z => ‖Sn n r z‖ₑ ^ 2 := (hSm n r hr).enorm.pow_const 2
    have := movd_holder_L2 (P.map (Zn n r)) (Qn n r) hac hq (le_max_right Cq 0)
      (hnorm.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) (hSm n r hr).aemeasurable hl (h1 r hr)
    rw [lintegral_map hmeas (hZn n r)] at this
    exact this
  -- per-`r` convergence
  have hper : ∀ r ∈ Set.Icc 0 T, Integrable (fun ω => R r (Z r ω)) P ∧
      Tendsto (fun n => ∫ z, Sn n r z ∂(P.map (Zn n r))) atTop (𝓝 (∫ z, R r z ∂(P.map (Z r)))) := by
    intro r hr
    have hmn : ∀ n, AEStronglyMeasurable (fun ω => Sn n r (Zn n r ω)) P := fun n =>
      ((hSm n r hr).comp (hZn n r)).aestronglyMeasurable
    obtain ⟨hint, hlim⟩ := movd_L1_conv hmn (B := B) (by
      filter_upwards [hL2] with n hn using hn r hr) (hpt r hr)
    refine ⟨hint, ?_⟩
    have e1 : ∀ n, ∫ z, Sn n r z ∂(P.map (Zn n r)) = ∫ ω, Sn n r (Zn n r ω) ∂P := fun n =>
      integral_map (hZn n r).aemeasurable (hSm n r hr).aestronglyMeasurable
    have e2 : ∫ z, R r z ∂(P.map (Z r)) = ∫ ω, R r (Z r ω) ∂P :=
      integral_map (hZ r).aemeasurable (hR r hr)
    simp_rw [e1, e2]
    exact hlim
  -- uniform bound
  have hbd : ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T, ‖∫ z, Sn n r z ∂(P.map (Zn n r))‖ ≤ 1 + B := by
    filter_upwards [hL2] with n hn r hr
    have hmn : AEStronglyMeasurable (fun ω => Sn n r (Zn n r ω)) P :=
      ((hSm n r hr).comp (hZn n r)).aestronglyMeasurable
    rw [integral_map (hZn n r).aemeasurable (hSm n r hr).aestronglyMeasurable]
    exact movd_abs_integral_le hmn hB0 (hn r hr)
  have hbdG : ∀ r ∈ Set.Icc 0 T, ‖∫ z, R r z ∂(P.map (Z r))‖ ≤ 1 + B := by
    intro r hr
    have h1 := (hper r hr).2.norm
    exact le_of_tendsto h1 (by filter_upwards [hbd] with n hn using hn r hr)
  -- measurability in `r`
  have hGm : ∀ n, AEStronglyMeasurable (fun r => ∫ z, Sn n r z ∂(P.map (Zn n r)))
      (volume.restrict (Set.Icc 0 T)) := fun n => (hGc n).aestronglyMeasurable measurableSet_Icc
  have hGlim : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)),
      Tendsto (fun n => ∫ z, Sn n r z ∂(P.map (Zn n r))) atTop (𝓝 (∫ z, R r z ∂(P.map (Z r)))) :=
    (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => (hper r hr).2)
  have hGmeas : AEStronglyMeasurable (fun r => ∫ z, R r z ∂(P.map (Z r)))
      (volume.restrict (Set.Icc 0 T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hGm hGlim
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · exact (integrable_map_measure (hR r hr) (hZ r).aemeasurable).2 (hper r hr).1
  · refine Integrable.of_bound (C := 1 + B) hGmeas ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hbdG)
  · intro t ht
    have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1 + B) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun n => (hGm n).mono_measure (Measure.restrict_mono hsub le_rfl)
    · filter_upwards [hbd] with n hn
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hn r (hsub hr))
    · exact (ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun r hr => (hper r (hsub hr)).2)

end HRS

end
