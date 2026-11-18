import HRS.MS.R2ChaosAux63

/-!
# HRS.MS.R2ChaosAux64 -- S9.6: measurability of `ζ ↦ r2IntPath T (f(·,ζ))` for an arbitrary jointly measurable `f`

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`r2IntPath` carries junk values (`0` if `u ↦ ∫_0^u f` is not continuous, e.g. if `f(·,ζ)` is not integrable); the event of continuity
is shown to be measurable through `s94_cont_of_rat_uc`.  This handles the processes with `N ≤ 1` (no moment hypotheses).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

section IntMeas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem s94_integral_Ioc_meas (f : ℝ × Ω → ℝ) (hf : Measurable f) (s : Set ℝ) :
    Measurable fun ζ => ∫ t in s, f (t, ζ) := by
  have hF : StronglyMeasurable fun p : Ω × ℝ => f (p.2, p.1) := (hf.comp measurable_swap).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict s)).measurable

theorem s94_gint_meas (f : ℝ × Ω → ℝ) (hf : Measurable f) (u : ℝ) :
    Measurable fun ζ => ∫ t in (0 : ℝ)..u, f (t, ζ) := by
  unfold intervalIntegral
  exact (s94_integral_Ioc_meas f hf _).sub (s94_integral_Ioc_meas f hf _)

theorem s94_cont_event_iff (T : ℝ) (hT : 0 ≤ T) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (Continuous fun u : Set.Icc (0 : ℝ) T => ∫ t in (0 : ℝ)..u, φ t) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q ∈ s94Qc T, ∀ q' ∈ s94Qc T, |q - q'| < 1 / ((m : ℝ) + 1) →
        |(∫ t in (0 : ℝ)..q, φ t) - ∫ t in (0 : ℝ)..q', φ t| ≤ 1 / ((n : ℝ) + 1) := by
  set g : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, φ t with hg
  constructor
  · intro hc
    have hcon : ContinuousOn g (Set.Icc 0 T) := continuousOn_iff_continuous_restrict.2 hc
    have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hcon)
    rw [Metric.uniformContinuousOn_iff] at huc
    intro n
    obtain ⟨δ, hδ, hδ'⟩ := huc (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun q hq q' hq' hqq => ?_⟩
    have hmem : ∀ x ∈ s94Qc T, x ∈ Set.Icc (0 : ℝ) T := by
      intro x hx
      rcases hx with ⟨-, h0, h1⟩ | h
      · exact ⟨h0, h1⟩
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact ⟨hT, le_rfl⟩
    have := hδ' q (hmem q hq) q' (hmem q' hq') (by rw [Real.dist_eq]; exact lt_trans hqq hm)
    rw [Real.dist_eq] at this
    exact this.le
  · intro hCs
    have hUC : ∀ ε > 0, ∃ δ > 0, ∀ q ∈ s94Qc T, ∀ q' ∈ s94Qc T, |q - q'| < δ → |g q - g q'| ≤ ε := by
      intro ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      obtain ⟨m, hm⟩ := hCs n
      refine ⟨1 / ((m : ℝ) + 1), by positivity, fun q hq q' hq' hqq => ?_⟩
      exact (hm q hq q' hq' hqq).trans hn.le
    have hcon : ContinuousOn g (Set.Icc 0 T) := by
      refine s94_cont_of_rat_uc hT (D := {u | IntegrableOn φ (Set.Ioc 0 u)}) ?_ ?_ ?_ hUC
      · intro u v hu hv0 hvu
        have hu' : IntegrableOn φ (Set.Ioc 0 u) volume := hu
        exact hu'.mono_set (Set.Ioc_subset_Ioc_right hvu)
      · intro u hu hu0 huT
        have hu' : IntegrableOn φ (Set.Ioc 0 u) volume := hu
        have hint : IntervalIntegrable φ volume 0 u :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hu0).2 hu'
        have := intervalIntegral.continuousOn_primitive_interval' (a := 0) hint
          (by rw [Set.uIcc_of_le hu0]; exact ⟨le_rfl, hu0⟩)
        rwa [Set.uIcc_of_le hu0] at this
      · intro u hu hu0 huT
        have hu' : ¬ IntegrableOn φ (Set.Ioc 0 u) volume := hu
        simp only [hg]
        rw [intervalIntegral.integral_of_le hu0, integral_undef hu']
    exact continuousOn_iff_continuous_restrict.1 hcon

theorem s94_measurable_r2IntPath (T : ℝ) (hT : 0 ≤ T) (f : ℝ × Ω → ℝ) (hf : Measurable f) :
    Measurable fun ζ => r2IntPath T (fun t => f (t, ζ)) := by
  classical
  haveI : Countable (s94Qc T) := (s94Qc_countable T).to_subtype
  set S : Set Ω := {ζ | Continuous fun u : Set.Icc (0 : ℝ) T => ∫ t in (0 : ℝ)..u, f (t, ζ)} with hS
  have hSm : MeasurableSet S := by
    have e : S = ⋂ n : ℕ, ⋃ m : ℕ, ⋂ q : s94Qc T, ⋂ q' : s94Qc T,
        {ζ | |(q : ℝ) - q'| < 1 / ((m : ℝ) + 1) →
          |(∫ t in (0 : ℝ)..q, f (t, ζ)) - ∫ t in (0 : ℝ)..q', f (t, ζ)| ≤ 1 / ((n : ℝ) + 1)} := by
      ext ζ
      simp only [hS, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Subtype.forall]
      exact s94_cont_event_iff T hT (fun t => f (t, ζ)) (hf.comp measurable_prodMk_right)
    rw [e]
    refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q =>
      MeasurableSet.iInter fun q' => ?_
    by_cases hc : |(q : ℝ) - q'| < 1 / ((m : ℝ) + 1)
    · simp only [hc, true_implies]
      exact measurableSet_le (((s94_gint_meas f hf q).sub (s94_gint_meas f hf q')).abs) measurable_const
    · have : {ζ : Ω | |(q : ℝ) - q'| < 1 / ((m : ℝ) + 1) →
          |(∫ t in (0 : ℝ)..q, f (t, ζ)) - ∫ t in (0 : ℝ)..q', f (t, ζ)| ≤ 1 / ((n : ℝ) + 1)} = Set.univ := by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hc
      rw [this]; exact MeasurableSet.univ
  refine ContinuousMap.measurable_iff_eval.2 fun u => ?_
  have hev : ∀ ζ, r2IntPath T (fun t => f (t, ζ)) u = if ζ ∈ S then ∫ t in (0 : ℝ)..(u : ℝ), f (t, ζ) else 0 := by
    intro ζ
    unfold r2IntPath r2ContPath
    by_cases h : ζ ∈ S
    · have h' : Continuous fun t : Set.Icc (0 : ℝ) T => ∫ s in (0 : ℝ)..(t : ℝ), f (s, ζ) := h
      rw [dif_pos h', if_pos h]
      rfl
    · have h' : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => ∫ s in (0 : ℝ)..(t : ℝ), f (s, ζ) := h
      rw [dif_neg h', if_neg h]
      rfl
  simp_rw [hev]
  exact Measurable.ite hSm (s94_gint_meas f hf u) measurable_const

end IntMeas

end HRS.MS.R2Chaos
