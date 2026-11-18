import HRS.MS.R26T8AS02
import HRS.MS.R26T8AS04a

/-!
# S8.2 observed-time layer, packet T8A.S06: triangular FTC for a parameter family of progressive integrands

Same route as S04 (`r26t8a_integrand_FTC`): S02 makes `v ↦ clip a v (Hd v)` an `L²`-valued map, the generic link lemma
`r26t8a_s04a_integral_ae` identifies the Bochner integral over `[a,t]` with the pointwise parameter integral, and the
triangular pointwise FTC (`r ≤ v ≤ t`) is applied after a null-set reduction.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_s06_hrest (a b : ℝ) (ha : 0 ≤ a) :
    (volume.restrict (Icc 0 b)).restrict (Icc a b) = volume.restrict (Icc a b) := by
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.2 (Icc_subset_Icc ha le_rfl)]

theorem r26t8a_s06_sq_clip {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) (a v b : ℝ) (ha : 0 ≤ a) (hvb : v ≤ b) (G : ℝ → Omega → I → ℝ) :
    sqIntegralOn P (r26t8a_clipIntegrand a v G) b = r26t8a_itoEnergy P G a v := by
  unfold sqIntegralOn r26t8a_itoEnergy
  refine lintegral_congr fun w => ?_
  have h : ∀ r, ∑ i, ‖r26t8a_clipIntegrand a v G r w i‖ₑ ^ 2 =
      (Icc a v).indicator (fun r => ∑ i, ‖G r w i‖ₑ ^ 2) r := by
    intro r
    by_cases hr : r ∈ Icc a v
    · simp [r26t8a_clipIntegrand, hr]
    · simp [r26t8a_clipIntegrand, hr]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.2 (Icc_subset_Icc ha hvb)]

theorem r26t8a_s06_diag {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) (F : Filtration ℝ mOmega) (a T t : ℝ) (ht : t ≤ a + T)
    (D : ℝ → Omega → I → ℝ) (hdiag : IsProgressiveL2 P F (r26t8a_clipIntegrand a (a + T) D)) :
    IsProgressiveL2 P F (r26t8a_clipIntegrand a t D) := by
  classical
  have heq : r26t8a_clipIntegrand a t D = fun r w =>
      if r ≤ t then r26t8a_clipIntegrand a (a + T) D r w else 0 := by
    funext r w i
    by_cases h1 : a ≤ r <;> by_cases h2 : r ≤ t
    · have h3 : r ≤ a + T := h2.trans ht
      simp [r26t8a_clipIntegrand, h1, h2, h3]
    · simp [r26t8a_clipIntegrand, h1, h2]
    · simp [r26t8a_clipIntegrand, h1, h2]
    · simp [r26t8a_clipIntegrand, h1, h2]
  refine ⟨?_, fun T' => ?_⟩
  · rw [heq]
    intro i
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (F i)]
        {p : Set.Iic i × Omega | (p.1 : ℝ) ≤ t} := by
      have : {p : Set.Iic i × Omega | (p.1 : ℝ) ≤ t} = {u : Set.Iic i | (u : ℝ) ≤ t} ×ˢ univ := by
        ext p; simp
      rw [this]
      exact MeasurableSet.prod (measurable_subtype_coe measurableSet_Iic) MeasurableSet.univ
    exact Measurable.ite hset (hdiag.prog i) measurable_const
  · refine lt_of_le_of_lt (sqIntegralOn_mono_of_enorm_le (fun r w k => ?_) T') (hdiag.sq T')
    rw [heq]
    by_cases h : r ≤ t
    · simp [h]
    · simp [h]

theorem r26t8a_s06_meas {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [SFinite P] (a T : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (Hd : ℝ → ℝ → Omega → I → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega =>
      if p.1.2 ≤ p.1.1 then Hd p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc a (a + T)))).prod P)) :
    AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega =>
      r26t8a_clipIntegrand a p.1.1 (Hd p.1.1) p.1.2 p.2)
      (((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))).prod P) := by
  classical
  have hA : MeasurableSet {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a (a + T)} :=
    (measurable_snd.comp measurable_fst) measurableSet_Icc
  have hmeas : (((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))).prod P).restrict
      {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a (a + T)} =
      ((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc a (a + T)))).prod P := by
    have e1 : (volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc a (a + T))) =
        ((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))).restrict
          ((univ : Set ℝ) ×ˢ Icc a (a + T)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, r26t8a_s06_hrest a (a + T) ha]
    rw [e1]
    have e2 := Measure.prod_restrict
      (μ := (volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))) (ν := P)
      ((univ : Set ℝ) ×ˢ Icc a (a + T)) univ
    rw [Measure.restrict_univ] at e2
    rw [e2]
    congr 1
    ext p
    simp
  have hf1 : AEStronglyMeasurable (Set.indicator {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a (a + T)}
      (fun p : (ℝ × ℝ) × Omega => if p.1.2 ≤ p.1.1 then Hd p.1.1 p.1.2 p.2 else 0))
      (((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))).prod P) := by
    rw [aestronglyMeasurable_indicator_iff hA, hmeas]
    exact hm
  refine hf1.congr ?_
  have hae : ∀ᵐ p ∂(((volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))).prod P),
      p.1.1 ∈ Icc a (a + T) := by
    have q1 := Measure.quasiMeasurePreserving_fst
      (μ := (volume.restrict (Icc a (a + T))).prod (volume.restrict (Icc 0 (a + T)))) (ν := P)
    have q2 := Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Icc a (a + T))) (ν := volume.restrict (Icc 0 (a + T)))
    exact (q2.comp q1).ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with p hp
  funext i
  simp only [Set.indicator_apply, r26t8a_clipIntegrand, mem_setOf_eq, mem_Icc]
  obtain ⟨hv1, hv2⟩ := hp
  by_cases h1 : a ≤ p.1.2 <;> by_cases h2 : p.1.2 ≤ p.1.1 <;> by_cases h3 : p.1.2 ≤ a + T <;>
    simp [h1, h2, h3] <;> linarith

theorem r26t8a_s06_ind {a r t : ℝ} (hat : a ≤ r) (f : ℝ → ℝ) (hf : IntegrableOn f (Icc r t)) :
    Integrable ((Ici r).indicator f) (volume.restrict (Icc a t)) ∧
      ∫ v in Icc a t, (Ici r).indicator f v = ∫ v in Icc r t, f v := by
  have hI : Icc a t ∩ Ici r = Icc r t := by
    ext v; simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨hat.trans h3, h2⟩, h3⟩
  refine ⟨?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici, Set.inter_comm, hI]
    exact hf
  · rw [setIntegral_indicator measurableSet_Ici, hI]

theorem r26t8a_s06_pointwise {Omega I : Type*} [Fintype I] (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (H Hd : ℝ → ℝ → Omega → I → ℝ) (r : ℝ) (x : Omega)
    (hgood : r ∈ Icc a b → ∀ i, IntegrableOn (fun v => Hd v r x i) (Icc r b) ∧
      ∀ t ∈ Icc r b, H t r x i = H r r x i + ∫ v in Icc r t, Hd v r x i) :
    (WithLp.toLp 2 (r26t8a_clipIntegrand a t (H t) r x) : EuclideanSpace ℝ I) =
      WithLp.toLp 2 (r26t8a_clipIntegrand a t (fun r w i => H r r w i) r x) +
        ∫ v in Icc a t,
          (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) r x) : EuclideanSpace ℝ I) := by
  by_cases hr : r ∈ Icc a t
  · have hg := hgood ⟨hr.1, hr.2.trans htb⟩
    have hint : ∀ i, Integrable (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) r x) :
        EuclideanSpace ℝ I) i) (volume.restrict (Icc a t)) := by
      intro i
      have e : (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) r x) :
          EuclideanSpace ℝ I) i) = (Ici r).indicator (fun v => Hd v r x i) := by
        funext v
        by_cases hv : r ≤ v
        · simp [r26t8a_clipIntegrand, hr.1, hv]
        · simp [r26t8a_clipIntegrand, hv]
      rw [e]
      exact (r26t8a_s06_ind hr.1 _
        ((hg i).1.mono_set (Icc_subset_Icc_right htb))).1
    ext i
    rw [PiLp.add_apply, eval_integral_piLp hint i]
    have e2 : (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) r x) :
          EuclideanSpace ℝ I) i) = (Ici r).indicator (fun v => Hd v r x i) := by
      funext v
      by_cases hv : r ≤ v
      · simp [r26t8a_clipIntegrand, hr.1, hv]
      · simp [r26t8a_clipIntegrand, hv]
    rw [e2, (r26t8a_s06_ind hr.1 _ ((hg i).1.mono_set (Icc_subset_Icc_right htb))).2]
    have := (hg i).2 t ⟨hr.2, htb⟩
    simp [r26t8a_clipIntegrand, hr, this]
  · have e : ∀ G : ℝ → Omega → I → ℝ, r26t8a_clipIntegrand a t G r x = 0 := by
      intro G
      funext i
      simp [r26t8a_clipIntegrand, hr]
    have e3 : ∀ v ∈ Icc a t, (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) r x) :
        EuclideanSpace ℝ I) = 0 := by
      intro v hv
      have : r ∉ Icc a v := fun h => hr ⟨h.1, h.2.trans hv.2⟩
      have e4 : r26t8a_clipIntegrand a v (Hd v) r x = 0 := by
        funext i
        simp [r26t8a_clipIntegrand, this]
      simp [e4]
    rw [setIntegral_congr_fun measurableSet_Icc e3]
    simp [e]

theorem r26t8a_triangle_FTC {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega)
    (a T : ℝ) (ha : 0≤a) (hT : 0<T) (H Hd : ℝ → ℝ → Omega → I → ℝ)
    (hdiag : IsProgressiveL2 P F (r26t8a_clipIntegrand a (a+T) (fun r w i => H r r w i)))
    (hH : ∀ t∈Set.Icc a (a+T), IsProgressiveL2 P F (r26t8a_clipIntegrand a t (H t)))
    (hHd : ∀ t∈Set.Icc a (a+T), IsProgressiveL2 P F (r26t8a_clipIntegrand a t (Hd t)))
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => if p.1.2≤p.1.1 then Hd p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc a (a+T))).prod (volume.restrict (Set.Icc a (a+T)))).prod P))
    (he : (∫⁻ v in Set.Icc a (a+T), r26t8a_itoEnergy P (Hd v) a v)<⊤)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc a (a+T))).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc p.1 (a+T)) ∧
      ∀ t∈Set.Icc p.1 (a+T), H t p.1 p.2 i=H p.1 p.1 p.2 i+∫ v in Set.Icc p.1 t, Hd v p.1 p.2 i) :
    ∃ V : ℝ → r26t8a_progSpan (I:=I) P F (a+T), IntegrableOn V (Set.Icc a (a+T)) ∧
      (∀ v (hv : v∈Set.Icc a (a+T)), V v=r26t8a_progEmbed P F (a+T)
        (r26t8a_clipIntegrand a v (Hd v)) (hHd v hv)) ∧
      ∀ t (ht : t∈Set.Icc a (a+T)), ∃ hD : IsProgressiveL2 P F (r26t8a_clipIntegrand a t (fun r w i => H r r w i)),
        r26t8a_progEmbed P F (a+T) (r26t8a_clipIntegrand a t (H t)) (hH t ht)=
          r26t8a_progEmbed P F (a+T) (r26t8a_clipIntegrand a t (fun r w i => H r r w i)) hD+
            ∫ v in Set.Icc a t, V v := by
  classical
  have hb : 0 ≤ a + T := by linarith
  haveI : IsFiniteMeasure (tsMeasure P (a + T)) := by unfold tsMeasure; infer_instance
  haveI hcs : CompleteSpace (r26t8a_progSpan (I := I) P F (a + T)) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hm' := r26t8a_s06_meas P a T ha hT Hd hm
  have he' : (∫⁻ v in Icc a (a + T),
      sqIntegralOn P (r26t8a_clipIntegrand a v (Hd v)) (a + T)) < ⊤ := by
    have h : (∫⁻ v in Icc a (a + T), sqIntegralOn P (r26t8a_clipIntegrand a v (Hd v)) (a + T)) =
        ∫⁻ v in Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v :=
      setLIntegral_congr_fun measurableSet_Icc
        (fun v hv => r26t8a_s06_sq_clip P a v (a + T) ha hv.2 (Hd v))
    rwa [h]
  obtain ⟨V, hVm, hVeq, hVn⟩ := r26t8a_integrand_sections P F (a + T) a (a + T) hb (by linarith)
    (fun v => r26t8a_clipIntegrand a v (Hd v)) hHd hm' he'
  have hVint : IntegrableOn V (Icc a (a + T)) := by
    refine ⟨hVm, ?_⟩
    have h1 : ∀ x : r26t8a_progSpan (I := I) P F (a + T), ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 2 := by
      intro x
      by_cases hx : ‖x‖ₑ ≤ 1
      · exact hx.trans le_self_add
      · push_neg at hx
        exact (le_self_pow₀ hx.le two_ne_zero).trans le_add_self
    show (∫⁻ t in Icc a (a + T), ‖V t‖ₑ) < ⊤
    calc (∫⁻ t in Icc a (a + T), ‖V t‖ₑ) ≤ ∫⁻ t in Icc a (a + T), (1 + ‖V t‖ₑ ^ 2) :=
          lintegral_mono fun t => h1 _
      _ = volume (Icc a (a + T)) + ∫⁻ t in Icc a (a + T), ‖V t‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const, lintegral_const]
          simp
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨measure_Icc_lt_top, ?_⟩
          rw [hVn]
          exact he'
  -- null-set reduction of the FTC hypothesis
  have hAm : MeasurableSet {q : ℝ × Omega | q.1 ∈ Icc a (a + T)} :=
    measurable_fst measurableSet_Icc
  have hmeasν : (tsMeasure P (a + T)).restrict {q : ℝ × Omega | q.1 ∈ Icc a (a + T)} =
      (volume.restrict (Icc a (a + T))).prod P := by
    have e1 : ∀ S : Set ℝ, (volume.restrict S).prod P = (volume.prod P).restrict (S ×ˢ univ) :=
      fun S => by
        have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := P) S univ
        rwa [Measure.restrict_univ] at this
    unfold tsMeasure
    rw [e1, e1, Measure.restrict_restrict hAm]
    congr 1
    ext ⟨s, x⟩
    simp only [mem_inter_iff, mem_setOf_eq, mem_prod, mem_Icc, mem_univ, and_true]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, ha.trans h.1, h.2⟩
  have hgood : ∀ᵐ q ∂(tsMeasure P (a + T)), q ∈ {q : ℝ × Omega | q.1 ∈ Icc a (a + T)} → ∀ i,
      IntegrableOn (fun t => Hd t q.1 q.2 i) (Icc q.1 (a + T)) ∧
      ∀ t ∈ Icc q.1 (a + T), H t q.1 q.2 i = H q.1 q.1 q.2 i + ∫ v in Icc q.1 t, Hd v q.1 q.2 i := by
    rw [← ae_restrict_iff' hAm, hmeasν]
    exact hFTC
  refine ⟨V, hVint, fun v hv => Subtype.ext ?_, fun t ht => ?_⟩
  · rw [hVeq v hv]
    rfl
  · have hD : IsProgressiveL2 P F (r26t8a_clipIntegrand a t (fun r w i => H r r w i)) :=
      r26t8a_s06_diag P F a T t ht.2 _ hdiag
    refine ⟨hD, ?_⟩
    have hsub : Icc a t ⊆ Icc a (a + T) := Icc_subset_Icc_right ht.2
    have hVc : IntegrableOn (fun v => ((V v : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T)))) (Icc a (a + T)) := by
      have := (Submodule.subtypeL (r26t8a_progSpan (I := I) P F (a + T))).integrable_comp hVint
      first | exact this | (convert this using 2)
    have hVct : Integrable (fun v => ((V v : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T)))) (volume.restrict (Icc a t)) :=
      hVc.mono_set hsub
    have hint : (((∫ v in Icc a t, V v) : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T))) =
        ∫ v in Icc a t, ((V v : r26t8a_progSpan (I := I) P F (a + T)) :
          Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T))) := by
      have := (Submodule.subtypeL (r26t8a_progSpan (I := I) P F (a + T))).integral_comp_comm
        (hVint.mono_set hsub)
      simpa using this.symm
    apply Subtype.ext
    change embL2 (hH t ht) (a + T) = embL2 hD (a + T) +
      (((∫ v in Icc a t, V v) : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T)))
    rw [hint]
    have hGm : AEStronglyMeasurable (Function.uncurry fun (v : ℝ) (q : ℝ × Omega) =>
        (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) q.1 q.2) : EuclideanSpace ℝ I))
        ((volume.restrict (Icc a t)).prod (tsMeasure P (a + T))) :=
      (r26t8a_s02_joint P (a + T) a (a + T) (fun v => r26t8a_clipIntegrand a v (Hd v)) hm').mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
    have hVG : ∀ᵐ v ∂(volume.restrict (Icc a t)),
        ⇑((V v : r26t8a_progSpan (I := I) P F (a + T)) :
          Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T))) =ᵐ[tsMeasure P (a + T)]
        fun q : ℝ × Omega => (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) q.1 q.2) :
          EuclideanSpace ℝ I) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [hVeq v (hsub hv)]
      exact r26t8a_s02_coe_ae P F (a + T) a (a + T) (fun v => r26t8a_clipIntegrand a v (Hd v)) hHd
        v (hsub hv)
    have hL := r26t8a_s04a_integral_ae (volume.restrict (Icc a t)) (tsMeasure P (a + T))
      (fun v => ((V v : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T)))) hVct
      (fun v q => (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) q.1 q.2) :
        EuclideanSpace ℝ I)) hGm hVG
    have hF' : ∀ᵐ q ∂(tsMeasure P (a + T)),
        (WithLp.toLp 2 (r26t8a_clipIntegrand a t (H t) q.1 q.2) : EuclideanSpace ℝ I) =
        WithLp.toLp 2 (r26t8a_clipIntegrand a t (fun r w i => H r r w i) q.1 q.2) +
          ∫ v in Icc a t,
            (WithLp.toLp 2 (r26t8a_clipIntegrand a v (Hd v) q.1 q.2) : EuclideanSpace ℝ I) := by
      filter_upwards [hgood] with q hq
      exact r26t8a_s06_pointwise a (a + T) t ht.1 ht.2 H Hd q.1 q.2 hq
    have cT := r26t8a_s02_coe_ae P F (a + T) a (a + T) (fun t => r26t8a_clipIntegrand a t (H t)) hH t ht
    have cD := r26t8a_s02_coe_ae P F (a + T) t t
      (fun _ => r26t8a_clipIntegrand a t (fun r w i => H r r w i)) (fun _ _ => hD) t ⟨le_rfl, le_rfl⟩
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (embL2 hD (a + T))
      (∫ v in Icc a t, ((V v : r26t8a_progSpan (I := I) P F (a + T)) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P (a + T)))), cT, cD, hL, hF'] with q h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, h4]
    exact h5

end HRS.MS.R26T8A

end
