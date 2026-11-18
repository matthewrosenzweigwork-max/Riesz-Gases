import HRS.Uniform.Q45Fam3

/-!
# Q45 (Lemma 3.20): assembling a vector measure from a dominated additive set function
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

theorem build_vm {X : Type*} [NormedAddCommGroup X] [CompleteSpace X] {T C : ℝ} (hC : 0 ≤ C)
    {tn : ℝ → ℝ} (htn0 : ∀ r, 0 ≤ tn r) (htni : IntegrableOn tn (Set.Icc 0 T)) (m : Set ℝ → X)
    (hm0 : ∀ I, ¬ MeasurableSet I → m I = 0)
    (hnorm : ∀ I, MeasurableSet I → ‖m I‖ ≤ C * ∫ r in I ∩ Set.Icc 0 T, tn r)
    (hadd : ∀ I I', MeasurableSet I → MeasurableSet I' → Disjoint I I' → m (I ∪ I') = m I + m I') :
    ∃ v : VectorMeasure ℝ X, (∀ I, v I = m I) ∧
      v.variation (Set.Icc 0 T) ≤ ENNReal.ofReal C * ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (tn r) ∧
      ContinuousOn (fun t => v (Set.Icc 0 t)) (Set.Icc 0 T) := by
  set ν : Measure ℝ := volume.restrict (Set.Icc 0 T) with hν
  set μ : Measure ℝ := ν.withDensity (fun r => ENNReal.ofReal C * ENNReal.ofReal (tn r)) with hμ
  have hfin : ∫⁻ r, ENNReal.ofReal (tn r) ∂ν ≠ ⊤ := htni.lintegral_lt_top.ne
  have hμs : ∀ s, MeasurableSet s → μ s = ENNReal.ofReal C * ∫⁻ r in s, ENNReal.ofReal (tn r) ∂ν := by
    intro s hs
    rw [hμ, withDensity_apply _ hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  haveI : IsFiniteMeasure μ := ⟨by
    rw [hμs _ MeasurableSet.univ, Measure.restrict_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)⟩
  have hdom : ∀ s, ‖m s‖ₑ ≤ μ s := by
    intro s
    by_cases hs : MeasurableSet s
    · rw [hμs s hs, hν, Measure.restrict_restrict hs]
      have hint : IntegrableOn tn (s ∩ Set.Icc 0 T) := htni.mono_set Set.inter_subset_right
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall htn0), ← ENNReal.ofReal_mul hC,
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hnorm s hs)
    · rw [hm0 s hs]; simp
  refine ⟨VectorMeasure.of_additive_of_le_measure m hdom hadd hm0, fun I => rfl, ?_, ?_⟩
  · have h1 := VectorMeasure.variation_le_of_forall_enorm_le
      (μ := VectorMeasure.of_additive_of_le_measure m hdom hadd hm0) (m := μ) (fun E _ => hdom E)
    refine (h1 (Set.Icc 0 T)).trans (le_of_eq ?_)
    rw [hμs _ measurableSet_Icc, hν, Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
  · intro t0 ht0
    set v := VectorMeasure.of_additive_of_le_measure m hdom hadd hm0 with hv
    have hmeasIcc : ∀ t, MeasurableSet (Set.Icc (0 : ℝ) t) := fun t => measurableSet_Icc
    -- bound by the measure of the increment
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖v (Set.Icc 0 t) - v (Set.Icc 0 t0)‖ ≤
        (μ (Set.Ioc (min t t0) (max t t0))).toReal := by
      intro t ht
      have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ‖m (Set.Icc 0 b) - m (Set.Icc 0 a)‖ ≤ (μ (Set.Ioc a b)).toReal := by
        intro a b ha hab
        have hu : Set.Icc (0 : ℝ) b = Set.Icc 0 a ∪ Set.Ioc a b := (Set.Icc_union_Ioc_eq_Icc ha hab).symm
        have hd : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) := by
          rw [Set.disjoint_left]; intro x h1 h2; exact absurd h1.2 (not_le.2 h2.1)
        have := hadd _ _ measurableSet_Icc measurableSet_Ioc hd
        rw [← hu] at this
        rw [this, add_sub_cancel_left, ← toReal_enorm]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (hdom _)
      rcases le_total t0 t with h | h
      · rw [min_eq_right h, max_eq_left h]
        exact key t0 t ht0.1 h
      · rw [min_eq_left h, max_eq_right h, norm_sub_rev]
        exact key t t0 ht.1 h
    have hlim : Tendsto (fun t => (μ (Set.Ioc (min t t0) (max t t0))).toReal) (𝓝 t0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => ν (Set.Ioc (min t t0) (max t t0))) (𝓝 t0) (𝓝 0) := by
        have hle : ∀ t : ℝ, ν (Set.Ioc (min t t0) (max t t0)) ≤ ENNReal.ofReal |t - t0| := by
          intro t
          calc ν (Set.Ioc (min t t0) (max t t0)) ≤ volume (Set.Ioc (min t t0) (max t t0)) :=
                Measure.restrict_le_self _
            _ = ENNReal.ofReal (max t t0 - min t t0) := Real.volume_Ioc
            _ = ENNReal.ofReal |t - t0| := by rw [max_sub_min_eq_abs']
        have h0 : Tendsto (fun t : ℝ => ENNReal.ofReal |t - t0|) (𝓝 t0) (𝓝 0) := by
          have : Tendsto (fun t : ℝ => |t - t0|) (𝓝 t0) (𝓝 0) := by
            have := ((continuous_id.sub continuous_const).abs (f := fun t : ℝ => t - t0)).tendsto t0
            simpa using this
          simpa using ENNReal.tendsto_ofReal this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun t => bot_le) hle
      have h2 := tendsto_setLIntegral_zero (μ := ν) (f := fun r => ENNReal.ofReal (tn r)) hfin
        (s := fun t : ℝ => Set.Ioc (min t t0) (max t t0)) h1
      have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) h2 (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at h3
      have h4 : Tendsto (fun t => (ENNReal.ofReal C * ∫⁻ r in Set.Ioc (min t t0) (max t t0),
          ENNReal.ofReal (tn r) ∂ν).toReal) (𝓝 t0) (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
        rwa [ENNReal.toReal_zero] at this
      refine h4.congr fun t => ?_
      rw [hμs _ measurableSet_Ioc]
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hbound t ht

end HRS.Uniform.Q45
