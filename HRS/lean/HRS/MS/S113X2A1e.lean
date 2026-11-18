import HRS.MS.S113X2A1d

/-!
# S11.3 X2 part A1e: the killed space-time measure through the exit time (Fubini)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_measurableSet_lt_stopping {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) < τ p.2} := by
  have hSeq : {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) < τ p.2} =
      ⋃ q : ℚ, ({r : ℝ | r < (q : ℝ)} ×ˢ {ζ | ((q : ℝ) : WithTop ℝ) < τ ζ}) := by
    ext ⟨r, ζ⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod]
    constructor
    · intro h
      by_cases htop : τ ζ = ⊤
      · obtain ⟨q, hq⟩ := exists_rat_gt r
        exact ⟨q, hq, by rw [htop]; exact WithTop.coe_lt_top _⟩
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 htop
        rw [← ha] at h
        have h' : r < a := by exact_mod_cast h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h'
        exact ⟨q, hq1, by rw [← ha]; exact_mod_cast hq2⟩
    · rintro ⟨q, hq1, hq2⟩
      exact lt_trans (by exact_mod_cast hq1) hq2
  rw [hSeq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.prod measurableSet_Iio ?_
  have : {ζ | ((q : ℝ) : WithTop ℝ) < τ ζ} = {ζ | τ ζ ≤ ((q : ℝ) : WithTop ℝ)}ᶜ := by
    ext ζ; simp
  rw [this]
  exact (ℱ.le _ _ (hτ (q : ℝ))).compl

open Classical in
theorem s113a_killed_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (X : ℝ≥0 → Ω → EucConfig d N) (hX0 : Measurable (X 0)) (hinit : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ)
    (hXm : Measurable fun z : ℝ × Ω => X z.1.toNNReal z.2)
    (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) (T : ℝ) (τ : Ω → WithTop ℝ)
    (hτs : MeasurableSet {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) < τ p.2})
    (hsurv : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ)
    (G : ℝ × EucConfig d N → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ p, p.1 ∈ Set.Ioo 0 T → |G p| ≤ C) :
    AEMeasurable (fun z : ℝ × Ω =>
      if z.2 ∈ s113a_survives D X z.1.toNNReal then ENNReal.ofReal (chi (X₀ z.2)) else 0)
      ((volume.restrict (Set.Ioo 0 T)).prod P) ∧
    IsFiniteMeasure (s113a_killedSpacetime P D X₀ X chi T) ∧
    Integrable G (s113a_killedSpacetime P D X₀ X chi T) ∧
    Integrable (fun ζ => chi (X 0 ζ) * (∫ r in Set.Ioo 0 T,
        (if ((r : ℝ) : WithTop ℝ) < τ ζ then G (r, X r.toNNReal ζ) else 0))) P ∧
    ∫ z, G z ∂(s113a_killedSpacetime P D X₀ X chi T) =
      ∫ ζ, chi (X 0 ζ) * (∫ r in Set.Ioo 0 T,
        (if ((r : ℝ) : WithTop ℝ) < τ ζ then G (r, X r.toNNReal ζ) else 0)) ∂P ∧
    ∫ z, G z ∂(s113a_killedSpacetime P D X₀ X chi T) =
      ∫ r in Set.Ioo 0 T, ∫ x, G (r, x) ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) ∧
    Integrable (fun r : ℝ => ∫ x, G (r, x) ∂(s113a_killedLaw P D X₀ X chi r.toNNReal))
      (volume.restrict (Set.Ioo 0 T)) := by
  set μ : Measure (ℝ × Ω) := (volume.restrict (Set.Ioo 0 T)).prod P with hμ
  set w : ℝ × Ω → ℝ≥0∞ := fun z =>
      if z.2 ∈ s113a_survives D X z.1.toNNReal then ENNReal.ofReal (chi (X₀ z.2)) else 0 with hw
  set w' : ℝ × Ω → ℝ≥0∞ := fun z =>
      if ((z.1 : ℝ) : WithTop ℝ) < τ z.2 then ENNReal.ofReal (chi (X 0 z.2)) else 0 with hw'
  have hw'm : Measurable w' :=
    Measurable.ite hτs (ENNReal.measurable_ofReal.comp (hchi.comp (hX0.comp measurable_snd)))
      measurable_const
  have hIoo : ∀ᵐ z ∂μ, z.1 ∈ Set.Ioo 0 T :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioo 0 T)) (ν := P)).ae
      (ae_restrict_mem measurableSet_Ioo)
  have hww : w =ᵐ[μ] w' := by
    have h1 := hIoo
    have h2 : ∀ᵐ z ∂μ, ∀ t : ℝ≥0, z.2 ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ z.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Ioo 0 T)) (ν := P)).ae hsurv
    have h3 : ∀ᵐ z ∂μ, X 0 z.2 = X₀ z.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Ioo 0 T)) (ν := P)).ae hinit
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    have e : ((z.1.toNNReal : ℝ≥0) : ℝ) = z.1 := Real.coe_toNNReal _ hz1.1.le
    simp only [hw, hw', hz3]
    have := hz2 z.1.toNNReal
    rw [e] at this
    by_cases hs : z.2 ∈ s113a_survives D X z.1.toNNReal
    · rw [if_pos hs, if_pos (this.1 hs)]
    · rw [if_neg hs, if_neg (fun h => hs (this.2 h))]
  have hfin : IsFiniteMeasure μ := inferInstance
  have hwle : ∀ z, w' z ≤ 1 := by
    intro z
    simp only [hw']
    split_ifs
    · exact ENNReal.ofReal_le_one.2 (hchi1 _)
    · exact bot_le
  have hfinw : IsFiniteMeasure (μ.withDensity w') := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ z, w' z ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono hwle
      _ = μ Set.univ := by simp
      _ < ⊤ := measure_lt_top _ _
  have hν : s113a_killedSpacetime P D X₀ X chi T =
      (μ.withDensity w').map (fun z => (z.1, X z.1.toNNReal z.2)) := by
    unfold s113a_killedSpacetime
    rw [withDensity_congr_ae hww]
  have hm : Measurable (fun z : ℝ × Ω => (z.1, X z.1.toNNReal z.2)) :=
    measurable_fst.prodMk hXm
  have hint : Integrable (fun z : ℝ × Ω => (w' z).toReal • G (z.1, X z.1.toNNReal z.2)) μ := by
    refine Integrable.of_bound (C := C) ?_ (hIoo.mono fun z hz => ?_)
    · exact ((ENNReal.measurable_toReal.comp hw'm).smul (hG.comp hm)).aestronglyMeasurable
    · have h1 : (w' z).toReal ≤ 1 := by
        have := hwle z
        simpa using ENNReal.toReal_mono (by simp) this
      have h0 : 0 ≤ (w' z).toReal := ENNReal.toReal_nonneg
      rw [norm_smul, Real.norm_of_nonneg h0, Real.norm_eq_abs]
      calc (w' z).toReal * |G (z.1, X z.1.toNNReal z.2)| ≤ 1 * C :=
            mul_le_mul h1 (hC _ hz) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
  have hslice : ∀ r ∈ Set.Ioo 0 T, ∫ x, G (r, x) ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) =
      ∫ ζ, (w' (r, ζ)).toReal • G (r, X r.toNNReal ζ) ∂P := by
    intro r hr
    have hXr : Measurable (X r.toNNReal) := hXm.comp (measurable_prodMk_left (x := r))
    have hwr : (fun ζ => if ζ ∈ s113a_survives D X r.toNNReal then ENNReal.ofReal (chi (X₀ ζ)) else 0)
        =ᵐ[P] fun ζ => w' (r, ζ) := by
      filter_upwards [hsurv, hinit] with ζ h1 h2
      have e : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1.le
      have := h1 r.toNNReal
      rw [e] at this
      simp only [hw', h2]
      by_cases hs : ζ ∈ s113a_survives D X r.toNNReal
      · rw [if_pos hs, if_pos (this.1 hs)]
      · rw [if_neg hs, if_neg (fun h => hs (this.2 h))]
    unfold s113a_killedLaw
    have hGr : AEStronglyMeasurable (fun x => G (r, x))
        (Measure.map (X r.toNNReal) (P.withDensity fun ζ => w' (r, ζ))) :=
      (hG.comp (measurable_prodMk_left (x := r))).aestronglyMeasurable
    rw [withDensity_congr_ae hwr, integral_map (f := fun x => G (r, x)) hXr.aemeasurable hGr,
      integral_withDensity_eq_integral_toReal_smul (f := fun ζ => w' (r, ζ))
        (g := fun ζ => G (r, X r.toNNReal ζ)) (hw'm.comp (measurable_prodMk_left (x := r)))
        (ae_of_all _ fun ζ => (by simp only [hw']; split_ifs <;> simp))]
  refine ⟨⟨w', hw'm, hww⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hν]; haveI := hfinw; infer_instance
  · rw [hν]
    refine Integrable.of_bound (C := C) hG.aestronglyMeasurable ?_
    have hset : MeasurableSet {p : ℝ × EucConfig d N | p.1 ∈ Set.Ioo 0 T} :=
      measurableSet_Ioo.preimage measurable_fst
    have hae : ∀ᵐ p ∂((μ.withDensity w').map (fun z => (z.1, X z.1.toNNReal z.2))),
        p.1 ∈ Set.Ioo 0 T := by
      rw [ae_map_iff hm.aemeasurable hset]
      exact (withDensity_absolutelyContinuous μ w').ae_le hIoo
    exact hae.mono fun p hp => by simpa using hC p hp
  · have hI2 := hint.swap.integral_prod_left
    refine hI2.congr (ae_of_all _ fun ζ => ?_)
    simp only [Function.comp]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    simp only [hw', Prod.swap]
    split_ifs
    · rw [ENNReal.toReal_ofReal (hchi0 _), smul_eq_mul]
    · simp
  · rw [hν, integral_map hm.aemeasurable hG.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hw'm (ae_of_all _ fun z => (by
        simp only [hw']; split_ifs <;> simp))]
    rw [hμ, integral_prod_symm _ hint]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    simp only [hw']
    split_ifs
    · rw [ENNReal.toReal_ofReal (hchi0 _), smul_eq_mul]
    · simp

  · rw [hν, integral_map hm.aemeasurable hG.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hw'm (ae_of_all _ fun z => (by
        simp only [hw']; split_ifs <;> simp))]
    rw [hμ, integral_prod _ hint]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr => (hslice r hr).symm
  · refine hint.integral_prod_left.congr ?_
    exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => (hslice r hr).symm)

end HRS.MS.S113X2

end
