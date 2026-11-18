import HRS.MS.FixEqP3Aux30

/-!
# S5.7 `fixed_equation` (worker S57P), part 43: measure-theoretic tools for the `L^p` assembly

measurability of `sup_{t ≤ T} ‖Z_t‖` for continuous paths, `L^p ≤ L^4` on a probability space, integrals of functions of one factor of a product measure.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

theorem s57p_sup_meas {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] {Z : ℝ → Ω → E} {T : ℝ} (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ ζ, ContinuousOn (fun t => Z t ζ) (Set.Icc 0 T)) :
    Measurable fun ζ => ⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ‖ₑ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  haveI : Countable D := hDc.to_subtype
  have heq : (fun ζ => ⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ‖ₑ) = fun ζ => ⨆ t : D, ‖Z t ζ‖ₑ := by
    funext ζ
    refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t : D => le_iSup (fun s : Set.Icc (0 : ℝ) T => ‖Z s ζ‖ₑ) t.1)
    have hmem : (t : Set.Icc (0 : ℝ) T) ∈ closure D := hDd t
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
    have hc : Tendsto (fun n => Z (u n : ℝ) ζ) atTop (𝓝 (Z t ζ)) :=
      ((hZc ζ t t.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨(continuous_subtype_val.tendsto _).comp hlim,
        Eventually.of_forall fun n => (u n).2⟩))
    have hc' : Tendsto (fun n => ‖Z (u n : ℝ) ζ‖ₑ) atTop (𝓝 ‖Z t ζ‖ₑ) := (continuous_enorm.tendsto _).comp hc
    exact le_of_tendsto' hc' fun n => le_iSup (fun s : D => ‖Z s ζ‖ₑ) ⟨u n, hu n⟩
  rw [heq]
  exact Measurable.iSup fun t : D => ((hZm t).enorm)

theorem s57p_jensen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f μ) {p : ℝ} (hp : p = 1 ∨ p = 2) :
    (∫⁻ ζ, f ζ ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ ζ, f ζ ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) := by
  have key : ∀ r : ℝ, 1 / p = 1 / 4 + 1 / r → 0 < p → p < 4 →
      (∫⁻ ζ, f ζ ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ ζ, f ζ ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ)) := by
    intro r hr hp0 hp4
    have := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr (p := p) (q := 4) (r := r) hp0 hp4 hr μ (f := f) (g := fun _ => 1) hf
      aemeasurable_const
    simpa using this
  rcases hp with rfl | rfl
  · exact key (4 / 3) (by norm_num) (by norm_num) (by norm_num)
  · exact key 4 (by norm_num) (by norm_num) (by norm_num)

theorem s57p_lint_fst {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] (P : Measure Ω) [SFinite P] (Q : Measure Ω₂)
    [IsProbabilityMeasure Q] {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ζ, f ζ.1 ∂(P.prod Q) = ∫⁻ x, f x ∂P := by
  rw [lintegral_prod (fun z : Ω × Ω₂ => f z.1) (hf.comp measurable_fst).aemeasurable]
  simp

theorem s57p_lint_snd {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω₂) [SFinite Q] {f : Ω₂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ζ, f ζ.2 ∂(P.prod Q) = ∫⁻ x, f x ∂Q := by
  rw [lintegral_prod (fun z : Ω × Ω₂ => f z.2) (hf.comp measurable_snd).aemeasurable]
  simp

/-- the (inner) lintegral of a function of the first factor, without measurability -/
theorem s57p_lint_fst_le {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] (P : Measure Ω) [SFinite P]
    (Q : Measure Ω₂) [IsProbabilityMeasure Q] (f : Ω → ℝ≥0∞) :
    ∫⁻ ζ, f ζ.1 ∂(P.prod Q) ≤ ∫⁻ x, f x ∂P := by
  rw [lintegral]
  refine iSup₂_le fun ψ hψ => ?_
  rw [← SimpleFunc.lintegral_eq_lintegral, lintegral_prod _ ψ.measurable.aemeasurable]
  refine lintegral_mono fun x => ?_
  calc ∫⁻ y, ψ (x, y) ∂Q ≤ ∫⁻ y, f x ∂Q := lintegral_mono fun y => hψ (x, y)
    _ = f x := by simp

end HRS.MS.FixEq
