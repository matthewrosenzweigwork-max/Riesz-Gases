import HRS.MS.R26T8AB00a3

/-!
# S8.2 observed-time layer, packet T8A.B00b (helper 1): measurability of the diagonal

In the triangular packet the diagonal `r ↦ V r r w` is a null set of the parameters, so its measurability on `[0,T] × Ω` is not part of
the hypotheses.  It follows from the FTC: on `{r ≤ t₀}` it is `V t₀ - ∫_r^{t₀} Vd`, for a time `t₀` with measurable slice, and
such times are dense; a countable exhaustion of `[0,T)` finishes.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00b1_clip_int (f : ℝ → ℝ) (r t : ℝ) (hr : 0 ≤ r) :
    ∫ v in Set.Icc 0 t, (if r ≤ v then f v else 0) = ∫ v in Set.Icc r t, f v := by
  have : (fun v => if r ≤ v then f v else 0) = (Set.Ici r).indicator f := by
    funext v
    by_cases h : r ≤ v
    · simp [h, Set.indicator_of_mem (show v ∈ Set.Ici r from h)]
    · simp [h, Set.indicator_of_notMem (show v ∉ Set.Ici r from h)]
  have hset : Set.Icc 0 t ∩ Set.Ici r = Set.Icc r t := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hr.trans h1, h2⟩, h1⟩
  rw [this, setIntegral_indicator measurableSet_Ici, hset]

theorem r26t8a_b00b1_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure (ℝ × Ω)) (f : ℝ × Ω → ℝ)
    (T : ℝ) (t : ℕ → ℝ) (ht : ∀ n : ℕ, T - 1 / ((n : ℝ) + 1) < t n)
    (hnull : μ {p | T ≤ p.1} = 0)
    (h : ∀ n, AEStronglyMeasurable f (μ.restrict {p : ℝ × Ω | p.1 ≤ t n})) :
    AEStronglyMeasurable f μ := by
  set U : Set (ℝ × Ω) := ⋃ n, {p : ℝ × Ω | p.1 ≤ t n} with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun n => measurableSet_le measurable_fst measurable_const
  have h1 : AEStronglyMeasurable f (μ.restrict U) := AEStronglyMeasurable.iUnion h
  have hsub : Uᶜ ⊆ {p : ℝ × Ω | T ≤ p.1} := by
    intro p hp
    simp only [hU, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hp
    by_contra hc
    rw [Set.mem_setOf_eq, not_le] at hc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
    have := ht n
    have := hp n
    linarith
  have h0 : μ.restrict Uᶜ = 0 := Measure.restrict_eq_zero.2 (measure_mono_null hsub hnull)
  have h2 : AEStronglyMeasurable f (μ.restrict Uᶜ) := by rw [h0]; exact aestronglyMeasurable_zero_measure f
  rw [← Measure.restrict_add_restrict_compl (μ := μ) hUm]
  exact h1.add_measure h2

theorem r26t8a_b00b1_diag_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (T : ℝ) (hT : 0 < T) (V Vd : ℝ → ℝ → Ω → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => if p.1.2 ≤ p.1.1 then V p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))).prod P))
    (hdm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Ω => if p.1.2 ≤ p.1.1 then Vd p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))).prod P))
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc 0 T)).prod P),
      IntegrableOn (fun v => Vd v p.1 p.2) (Set.Icc p.1 T) ∧
      ∀ t ∈ Set.Icc p.1 T, V t p.1 p.2 = V p.1 p.1 p.2 + ∫ v in Set.Icc p.1 t, Vd v p.1 p.2) :
    AEStronglyMeasurable (fun p : ℝ × Ω => V p.1 p.1 p.2)
      ((volume.restrict (Set.Icc 0 T)).prod P) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc 0 T) with hμT
  have hm' := r26t8a_b00n2_assoc P μT μT (fun t r w => if r ≤ t then V t r w else 0) hm
  have hgood := hm'.prodMk_left
  have hprim := fun t0 (ht0 : t0 ∈ Set.Icc 0 T) => r26t8a_b00a1_prim_meas P 0 T T t0 ht0
    (fun v r w => if r ≤ v then Vd v r w else 0) hdm
  have hex : ∀ n : ℕ, ∃ t ∈ Set.Icc 0 T, T - 1 / ((n : ℝ) + 1) < t ∧
      AEStronglyMeasurable (fun y : ℝ × Ω => if y.1 ≤ t then V t y.1 y.2 else 0) (μT.prod P) := by
    intro n
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    set a : ℝ := max 0 (T - 1 / ((n : ℝ) + 1)) with ha
    have haT : a < T := max_lt hT (by linarith)
    have hne : (μT.restrict (Set.Ioc a T)) ≠ 0 := by
      intro h0
      have := congrArg (fun m : Measure ℝ => m Set.univ) h0
      simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at this
      rw [hμT, Measure.restrict_apply measurableSet_Ioc,
        Set.inter_eq_left.mpr (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left (le_max_left _ _)))
          ] at this
      rw [Real.volume_Ioc] at this
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 haT)).ne' this
    have : (ae (μT.restrict (Set.Ioc a T))).NeBot := ae_neBot.mpr hne
    have hmem : ∀ᵐ t ∂(μT.restrict (Set.Ioc a T)), t ∈ Set.Ioc a T := ae_restrict_mem measurableSet_Ioc
    have hg2 := ae_restrict_of_ae (s := Set.Ioc a T) hgood
    obtain ⟨t, htB, htg⟩ := (hmem.and hg2).exists
    exact ⟨t, ⟨(le_max_left _ _).trans htB.1.le, htB.2⟩, lt_of_le_of_lt (le_max_right _ _) htB.1, htg⟩
  choose t ht using hex
  have hnull : (μT.prod P) {p : ℝ × Ω | T ≤ p.1} = 0 := by
    have : {p : ℝ × Ω | T ≤ p.1} = Set.Ici T ×ˢ Set.univ := by ext p; simp
    rw [this, Measure.prod_prod]
    have h1 : μT (Set.Ici T) = 0 := by
      rw [hμT, Measure.restrict_apply measurableSet_Ici]
      refine measure_mono_null (t := {T}) (fun x hx => ?_) Real.volume_singleton
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_singleton_iff] at hx ⊢
      linarith [hx.1, hx.2.2]
    rw [h1, zero_mul]
  refine r26t8a_b00b1_union (μT.prod P) _ T t (fun n => (ht n).2.1) hnull fun n => ?_
  have hg := (ht n).2.2.sub (hprim (t n) (ht n).1)
  have hae0 : ∀ᵐ p ∂(μT.prod P), p.1 ∈ Set.Icc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  refine (hg.mono_measure Measure.restrict_le_self).congr ?_
  refine (ae_restrict_iff' (measurableSet_le measurable_fst measurable_const)).2 ?_
  filter_upwards [hFTC, hae0] with p hp hp0 hle
  have hle' : p.1 ≤ t n := hle
  have hFT := hp.2 (t n) ⟨hle', (ht n).1.2⟩
  simp only [Pi.sub_apply, hle', if_true]
  rw [r26t8a_b00b1_clip_int (fun v => Vd v p.1 p.2) p.1 (t n) hp0.1, hFT]
  ring

end HRS.MS.R26T8A

end
