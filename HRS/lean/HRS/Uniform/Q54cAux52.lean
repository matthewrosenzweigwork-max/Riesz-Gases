import Mathlib

/-!
# Q54c, part 52: a real-variable lemma on integrals with junk value

If `f t - f 0 = ∫_{[0,t]} G` for all `t ∈ [0,T]` for a bounded `G` (Bochner integral, junk value `0` when `G`
is not a.e. strongly measurable on `[0,t]`), then `f` is a.e. equal on `[0,T]` to a measurable function
(piecewise continuous), and `f` is continuous on `[0,T]` if `G` is a.e. strongly measurable on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

theorem junk_interval {T : ℝ} (hT : 0 ≤ T) (G f : ℝ → ℝ) {C : ℝ} (hC : ∀ r ∈ Icc (0 : ℝ) T, |G r| ≤ C)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, f t - f 0 = ∫ r in Icc (0 : ℝ) t, G r) :
    ∃ t₀ ∈ Icc (0 : ℝ) T, ContinuousOn f (Icc 0 t₀) ∧ (∀ t ∈ Ioc t₀ T, f t = f 0) ∧
      (∀ t ∈ Ioc t₀ T, ¬ AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) t))) := by
  set S : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) t))} with hS
  have h0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, hT⟩, ?_⟩
    have : volume.restrict (Icc (0 : ℝ) 0) = 0 := by
      rw [Icc_self]; exact Measure.restrict_eq_zero.2 (measure_singleton _)
    rw [this]; exact aestronglyMeasurable_zero_measure _
  have hbdd : BddAbove S := ⟨T, fun t ht => ht.1.2⟩
  have hdown : ∀ t ∈ S, ∀ t' ∈ Icc (0 : ℝ) t, t' ∈ S := by
    intro t ht t' ht'
    refine ⟨⟨ht'.1, ht'.2.trans ht.1.2⟩, ht.2.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right ht'.2) le_rfl)⟩
  set t₀ := sSup S with ht₀
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := ⟨le_csSup hbdd h0, csSup_le ⟨0, h0⟩ fun t ht => ht.1.2⟩
  have ht₀S : t₀ ∈ S := by
    by_cases hz : t₀ = 0
    · rw [hz]; exact h0
    have hpos : 0 < t₀ := lt_of_le_of_ne ht₀mem.1 (Ne.symm hz)
    refine ⟨ht₀mem, ?_⟩
    have hn : ∀ n : ℕ, AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) (t₀ - 1 / ((n : ℝ) + 1)))) := by
      intro n
      by_cases hneg : t₀ - 1 / ((n : ℝ) + 1) < 0
      · rw [Icc_eq_empty (by linarith)]
        simp
      · push Not at hneg
        obtain ⟨s, hs, hlt⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (show t₀ - 1 / ((n : ℝ) + 1) < t₀ by
          have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
        exact (hdown s hs _ ⟨hneg, hlt.le⟩).2
    have hU : AEStronglyMeasurable G (volume.restrict (⋃ n : ℕ, Icc (0 : ℝ) (t₀ - 1 / ((n : ℝ) + 1)))) :=
      (aestronglyMeasurable_iUnion_iff).2 hn
    have hsub : Icc (0 : ℝ) t₀ ⊆ (⋃ n : ℕ, Icc (0 : ℝ) (t₀ - 1 / ((n : ℝ) + 1))) ∪ {t₀} := by
      intro x hx
      by_cases hxt : x = t₀
      · exact Or.inr hxt
      · left
        have hlt : x < t₀ := lt_of_le_of_ne hx.2 hxt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        exact Set.mem_iUnion.2 ⟨n, hx.1, by linarith⟩
    have hsing : AEStronglyMeasurable G (volume.restrict ({t₀} : Set ℝ)) := by
      have : volume.restrict ({t₀} : Set ℝ) = 0 := Measure.restrict_eq_zero.2 (measure_singleton _)
      rw [this]; exact aestronglyMeasurable_zero_measure _
    have hun := (aestronglyMeasurable_union_iff).2 ⟨hU, hsing⟩
    exact hun.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨t₀, ht₀mem, ?_, ?_, ?_⟩
  · have hint : IntegrableOn G (Icc (0 : ℝ) t₀) := by
      refine Integrable.of_bound ht₀S.2 C ?_
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs]; exact hC r ⟨hr.1, hr.2.trans ht₀mem.2⟩
    have hint' : IntegrableOn G (uIcc (0 : ℝ) t₀) := by rwa [uIcc_of_le ht₀mem.1]
    have hc := intervalIntegral.continuousOn_primitive_interval hint'
    rw [uIcc_of_le ht₀mem.1] at hc
    have e : ∀ t ∈ Icc (0 : ℝ) t₀, f t = f 0 + ∫ x in (0 : ℝ)..t, G x := by
      intro t ht
      have := hf t ⟨ht.1, ht.2.trans ht₀mem.2⟩
      rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
      linarith
    exact (continuousOn_const.add hc).congr e
  · intro t ht
    have hnS : t ∉ S := fun h => absurd (le_csSup hbdd h) (not_le.2 ht.1)
    have hnm : ¬ AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) t)) := fun h =>
      hnS ⟨⟨(ht₀mem.1.trans ht.1.le), ht.2⟩, h⟩
    have := hf t ⟨ht₀mem.1.trans ht.1.le, ht.2⟩
    rw [integral_non_aestronglyMeasurable hnm] at this
    linarith
  · intro t ht h
    exact (show t ∉ S from fun h' => absurd (le_csSup hbdd h') (not_le.2 ht.1))
      ⟨⟨(ht₀mem.1.trans ht.1.le), ht.2⟩, h⟩

theorem junk_interval_measurable {T : ℝ} (hT : 0 ≤ T) (G f : ℝ → ℝ) {C : ℝ}
    (hC : ∀ r ∈ Icc (0 : ℝ) T, |G r| ≤ C)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, f t - f 0 = ∫ r in Icc (0 : ℝ) t, G r) :
    ∃ f' : ℝ → ℝ, Measurable f' ∧ ∀ t ∈ Icc (0 : ℝ) T, f' t = f t := by
  obtain ⟨t₀, ht₀, hc, hconst, -⟩ := junk_interval hT G f hC hf
  have h0 : (0 : ℝ) ≤ t₀ := ht₀.1
  have hcont : Continuous (fun t : ℝ => f (projIcc 0 t₀ h0 t : ℝ)) :=
    hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc 0 t₀ h0 t).2)
  refine ⟨fun t => if t ≤ t₀ then f (projIcc 0 t₀ h0 t : ℝ) else f 0, ?_, ?_⟩
  · exact Measurable.ite measurableSet_Iic hcont.measurable measurable_const
  · intro t ht
    by_cases h : t ≤ t₀
    · simp only [h, ite_true]
      rw [projIcc_of_mem h0 ⟨ht.1, h⟩]
    · simp only [h, ite_false]
      exact (hconst t ⟨not_le.1 h, ht.2⟩).symm

theorem junk_interval_continuousOn {T : ℝ} (hT : 0 ≤ T) (G f : ℝ → ℝ) {C : ℝ}
    (hC : ∀ r ∈ Icc (0 : ℝ) T, |G r| ≤ C)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, f t - f 0 = ∫ r in Icc (0 : ℝ) t, G r)
    (hm : AEStronglyMeasurable G (volume.restrict (Icc (0 : ℝ) T))) : ContinuousOn f (Icc 0 T) := by
  obtain ⟨t₀, ht₀, hc, hconst, hnm⟩ := junk_interval hT G f hC hf
  have : t₀ = T := by
    by_contra h
    exact hnm T ⟨lt_of_le_of_ne ht₀.2 h, le_rfl⟩ hm
  rwa [this] at hc

end HRS.Uniform.Q54c
