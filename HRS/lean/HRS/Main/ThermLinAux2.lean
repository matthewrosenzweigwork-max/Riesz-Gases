import Mathlib

/-!
# THERMLIN, part 2: a measurable version of an a.e. continuous process

A process `Z : ℝ → Ω → E` whose sections are only a.e. measurable for `t ∈ [0,T]` and whose paths are a.e. continuous
on `[0,T]` has a modification `Zm` (equal a.s. at every fixed `t ∈ [0,T]`, indistinguishable from `Z` on a
full-measure event, equal to `Z` clamped to `[0,T]`) all of whose sections are measurable.  Used to satisfy the
`∀ t, Measurable (Y t)` field of `IsLinearFluctuationSolution`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.ThermLin

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The clamp of `t` to `[0,T]`. -/
def thermlinClamp (T t : ℝ) : ℝ := max 0 (min T t)

theorem thermlinClamp_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : thermlinClamp T t ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

theorem thermlinClamp_of_mem {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : thermlinClamp T t = t := by
  unfold thermlinClamp
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem thermlinClamp_continuous (T : ℝ) : Continuous (thermlinClamp T) := by
  unfold thermlinClamp; fun_prop

/-- A measurable-sections modification of an a.e. continuous process. -/
theorem thermlin_measurable_version {P : Measure Ω} {T : ℝ} (hT : 0 ≤ T) [SecondCountableTopology E]
    (Z : ℝ → Ω → E) (hm : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc 0 T)) :
    ∃ Zm : ℝ → Ω → E, (∀ t, Measurable (Zm t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Zm t ω) (Icc 0 T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, Zm t =ᵐ[P] Z t) := by
  classical
  -- measurable representatives at the rational times
  have hq : ∀ q : ℚ, ∃ f : Ω → E, Measurable f ∧ f =ᵐ[P] Z (thermlinClamp T q) := fun q =>
    ⟨(hm _ (thermlinClamp_mem hT q)).mk _, (hm _ (thermlinClamp_mem hT q)).measurable_mk,
      (hm _ (thermlinClamp_mem hT q)).ae_eq_mk.symm⟩
  choose Zq hZqm hZqae using hq
  have h2 : ∀ᵐ ω ∂P, ∀ q : ℚ, Zq q ω = Z (thermlinClamp T q) ω := ae_all_iff.2 hZqae
  have hgood := hc.and h2
  obtain ⟨Nb, hNbsub, hNbm, hNb0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hmem : ∀ ω, ω ∉ Nb → ContinuousOn (fun t => Z t ω) (Icc 0 T) ∧
      ∀ q : ℚ, Zq q ω = Z (thermlinClamp T q) ω := by
    intro ω hω
    by_contra hcon
    exact hω (hNbsub hcon)
  refine ⟨fun t => Nbᶜ.indicator (fun ω => Z (thermlinClamp T t) ω), fun t => ?_, ?_, ?_⟩
  · -- measurability as a pointwise limit
    obtain ⟨x, hxr, hxt⟩ := mem_closure_iff_seq_limit.1
      (show t ∈ closure (range ((↑) : ℚ → ℝ)) by rw [Rat.denseRange_cast.closure_range]; exact mem_univ t)
    choose q hq using hxr
    have hqt : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 t) := by
      simpa [hq] using hxt
    refine measurable_of_tendsto_metrizable
      (f := fun n => Nbᶜ.indicator (Zq (q n))) (fun n => (hZqm (q n)).indicator hNbm.compl) ?_
    refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hω : ω ∈ Nb
    · simp [hω]
    · have hωc : ω ∈ Nbᶜ := hω
      obtain ⟨hcont, hZq⟩ := hmem ω hω
      simp only [Set.indicator_of_mem hωc, hZq]
      have h1 : Tendsto (fun n => thermlinClamp T ((q n : ℚ) : ℝ)) atTop (𝓝 (thermlinClamp T t)) :=
        ((thermlinClamp_continuous T).tendsto t).comp hqt
      have h3 : Tendsto (fun n => thermlinClamp T ((q n : ℚ) : ℝ)) atTop
          (𝓝[Icc 0 T] (thermlinClamp T t)) :=
        tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => thermlinClamp_mem hT _⟩
      exact (hcont.continuousWithinAt (thermlinClamp_mem hT t)).tendsto.comp h3
  · filter_upwards [compl_mem_ae_iff.2 hNb0] with ω hω
    obtain ⟨hcont, -⟩ := hmem ω hω
    refine hcont.congr fun t ht => ?_
    simp [Set.indicator_of_mem (show ω ∈ Nbᶜ from hω), thermlinClamp_of_mem ht]
  · intro t ht
    filter_upwards [compl_mem_ae_iff.2 hNb0] with ω hω
    simp [Set.indicator_of_mem (show ω ∈ Nbᶜ from hω), thermlinClamp_of_mem ht]

end HRS.ThermLin
