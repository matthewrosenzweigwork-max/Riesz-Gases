import HRS.MS.R26T8AS02
import HRS.MS.R26T8AS04a

/-!
# S8.2 observed-time layer, packet T8A.S04: Bochner FTC for a parameter family of progressive integrands

The parameter map `t ↦ clip (Hd t)` is made `L²`-valued by `r26t8a_integrand_sections` (S02); the generic link
lemma `r26t8a_s04a_integral_ae` identifies the `Lp`-valued Bochner integral with the pointwise parameter integral,
to which the a.e. pointwise FTC (after clipping and a null-set reduction) applies.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_s04_hrest (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume.restrict (Icc 0 b)).restrict (Icc a b) = volume.restrict (Icc a b) := by
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.2 (Icc_subset_Icc ha le_rfl)]

theorem r26t8a_s04_sq_clip {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (G : ℝ → Omega → I → ℝ) :
    sqIntegralOn P (r26t8a_clipIntegrand a b G) b = r26t8a_itoEnergy P G a b := by
  unfold sqIntegralOn r26t8a_itoEnergy
  refine lintegral_congr fun w => ?_
  have h : ∀ r, ∑ i, ‖r26t8a_clipIntegrand a b G r w i‖ₑ ^ 2 =
      (Icc a b).indicator (fun r => ∑ i, ‖G r w i‖ₑ ^ 2) r := by
    intro r
    by_cases hr : r ∈ Icc a b
    · simp [r26t8a_clipIntegrand, hr]
    · simp [r26t8a_clipIntegrand, hr]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Icc, r26t8a_s04_hrest a b ha hab]

theorem r26t8a_s04_clip_meas {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [SFinite P] (a b T : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (Hd : ℝ → ℝ → Omega → I → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega => Hd p.1.1 p.1.2 p.2)
      (((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc a b))).prod P)) :
    AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega =>
      r26t8a_clipIntegrand a b (Hd p.1.1) p.1.2 p.2)
      (((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 b))).prod P) := by
  classical
  have hA : MeasurableSet {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a b} :=
    (measurable_snd.comp measurable_fst) measurableSet_Icc
  have hmeas : (((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 b))).prod P).restrict
      {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a b} =
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc a b))).prod P := by
    have e1 : (volume.restrict (Icc 0 T)).prod (volume.restrict (Icc a b)) =
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 b))).restrict
          ((univ : Set ℝ) ×ˢ Icc a b) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, r26t8a_s04_hrest a b ha hab]
    rw [e1]
    have e2 := Measure.prod_restrict
      (μ := (volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 b))) (ν := P)
      ((univ : Set ℝ) ×ˢ Icc a b) univ
    rw [Measure.restrict_univ] at e2
    rw [e2]
    congr 1
    ext p
    simp
  have hind : (fun p : (ℝ × ℝ) × Omega => r26t8a_clipIntegrand a b (Hd p.1.1) p.1.2 p.2) =
      Set.indicator {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a b}
        (fun p => Hd p.1.1 p.1.2 p.2) := by
    funext p
    by_cases h : p.1.2 ∈ Icc a b
    · rw [Set.indicator_of_mem (show p ∈ {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a b} from h)]
      funext i
      simp [r26t8a_clipIntegrand, h]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (ℝ × ℝ) × Omega | p.1.2 ∈ Icc a b} from h)]
      funext i
      simp [r26t8a_clipIntegrand, h]
  rw [hind, aestronglyMeasurable_indicator_iff hA, hmeas]
  exact hm

theorem r26t8a_s04_pointwise {Omega I : Type*} [Fintype I] (a b T t : ℝ) (ht : t ∈ Icc 0 T)
    (H Hd : ℝ → ℝ → Omega → I → ℝ) (s : ℝ) (x : Omega)
    (hgood : s ∈ Icc a b → ∀ i, IntegrableOn (fun v => Hd v s x i) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, H t s x i = H 0 s x i + ∫ v in Icc 0 t, Hd v s x i) :
    (WithLp.toLp 2 (r26t8a_clipIntegrand a b (H t) s x) : EuclideanSpace ℝ I) =
      WithLp.toLp 2 (r26t8a_clipIntegrand a b (H 0) s x) +
        ∫ v in Icc 0 t,
          (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) s x) : EuclideanSpace ℝ I) := by
  by_cases hs : s ∈ Icc a b
  · have hg := hgood hs
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hint : ∀ i, Integrable (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) s x) :
        EuclideanSpace ℝ I) i) (volume.restrict (Icc 0 t)) := by
      intro i
      have e : (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) s x) :
          EuclideanSpace ℝ I) i) = fun v => Hd v s x i := by
        funext v
        simp [r26t8a_clipIntegrand, hs]
      rw [e]
      exact (hg i).1.mono_set hsub
    ext i
    rw [PiLp.add_apply, eval_integral_piLp hint i]
    have e2 : (fun v => (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) s x) :
          EuclideanSpace ℝ I) i) = fun v => Hd v s x i := by
      funext v
      simp [r26t8a_clipIntegrand, hs]
    rw [e2]
    simp [r26t8a_clipIntegrand, hs, (hg i).2 t ht]
  · have e : ∀ G : ℝ → Omega → I → ℝ, r26t8a_clipIntegrand a b G s x = 0 := by
      intro G
      funext i
      simp [r26t8a_clipIntegrand, hs]
    simp only [e]
    simp

theorem r26t8a_integrand_FTC {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega)
    (a b T : ℝ) (ha : 0≤a) (hab : a≤b) (hT : 0<T)
    (H Hd : ℝ → ℝ → Omega → I → ℝ)
    (hH : ∀ t∈Set.Icc 0 T, IsProgressiveL2 P F (r26t8a_clipIntegrand a b (H t)))
    (hHd : ∀ t∈Set.Icc 0 T, IsProgressiveL2 P F (r26t8a_clipIntegrand a b (Hd t)))
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => Hd p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc a b))).prod P))
    (he : (∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) a b)<⊤)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc 0 T) ∧
      ∀ t∈Set.Icc 0 T, H t p.1 p.2 i=H 0 p.1 p.2 i+∫ v in Set.Icc 0 t, Hd v p.1 p.2 i) :
    ∃ V : ℝ → r26t8a_progSpan (I:=I) P F b, IntegrableOn V (Set.Icc 0 T) ∧
      (∀ t (ht : t∈Set.Icc 0 T),
        V t=r26t8a_progEmbed P F b (r26t8a_clipIntegrand a b (Hd t)) (hHd t ht)) ∧
      (∀ t (ht : t∈Set.Icc 0 T),
        r26t8a_progEmbed P F b (r26t8a_clipIntegrand a b (H t)) (hH t ht)=
          r26t8a_progEmbed P F b (r26t8a_clipIntegrand a b (H 0)) (hH 0 ⟨le_rfl,le_of_lt hT⟩)+
            ∫ v in Set.Icc 0 t, V v) := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  haveI : IsFiniteMeasure (tsMeasure P b) := by unfold tsMeasure; infer_instance
  haveI hcs : CompleteSpace (r26t8a_progSpan (I := I) P F b) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hm' := r26t8a_s04_clip_meas P a b T ha hab Hd hm
  have he' : (∫⁻ t in Icc 0 T, sqIntegralOn P (r26t8a_clipIntegrand a b (Hd t)) b) < ⊤ := by
    have h : (∫⁻ t in Icc 0 T, sqIntegralOn P (r26t8a_clipIntegrand a b (Hd t)) b) =
        ∫⁻ t in Icc 0 T, r26t8a_itoEnergy P (Hd t) a b :=
      lintegral_congr fun t => r26t8a_s04_sq_clip P a b ha hab (Hd t)
    rwa [h]
  obtain ⟨V, hVm, hVeq, hVn⟩ := r26t8a_integrand_sections P F b 0 T hb hT.le
    (fun t => r26t8a_clipIntegrand a b (Hd t)) hHd hm' he'
  have hVint : IntegrableOn V (Icc 0 T) := by
    refine ⟨hVm, ?_⟩
    have h1 : ∀ x : r26t8a_progSpan (I := I) P F b, ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 2 := by
      intro x
      by_cases hx : ‖x‖ₑ ≤ 1
      · exact hx.trans le_self_add
      · push_neg at hx
        exact (le_self_pow₀ hx.le two_ne_zero).trans le_add_self
    show (∫⁻ t in Icc 0 T, ‖V t‖ₑ) < ⊤
    calc (∫⁻ t in Icc 0 T, ‖V t‖ₑ) ≤ ∫⁻ t in Icc 0 T, (1 + ‖V t‖ₑ ^ 2) :=
          lintegral_mono fun t => h1 _
      _ = volume (Icc 0 T) + ∫⁻ t in Icc 0 T, ‖V t‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const, lintegral_const]
          simp
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨measure_Icc_lt_top, ?_⟩
          rw [hVn]
          exact he'
  -- null-set reduction of the FTC hypothesis
  have hAm : MeasurableSet {q : ℝ × Omega | q.1 ∈ Icc a b} := measurable_fst measurableSet_Icc
  have hmeasν : (tsMeasure P b).restrict {q : ℝ × Omega | q.1 ∈ Icc a b} =
      (volume.restrict (Icc a b)).prod P := by
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
  have hgood : ∀ᵐ q ∂(tsMeasure P b), q ∈ {q : ℝ × Omega | q.1 ∈ Icc a b} → ∀ i,
      IntegrableOn (fun t => Hd t q.1 q.2 i) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, H t q.1 q.2 i = H 0 q.1 q.2 i + ∫ v in Icc 0 t, Hd v q.1 q.2 i := by
    rw [← ae_restrict_iff' hAm, hmeasν]
    exact hFTC
  refine ⟨V, hVint, fun t ht => Subtype.ext ?_, fun t ht => ?_⟩
  · rw [hVeq t ht]
    rfl
  · have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have hVc : IntegrableOn (fun v => ((V v : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))) (Icc 0 T) :=
      by
        have := (Submodule.subtypeL (r26t8a_progSpan (I := I) P F b)).integrable_comp hVint
        first | exact this | (convert this using 2)
    have hVct : Integrable (fun v => ((V v : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))) (volume.restrict (Icc 0 t)) :=
      hVc.mono_set hsub
    have hint : (((∫ v in Icc 0 t, V v) : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b)) =
        ∫ v in Icc 0 t, ((V v : r26t8a_progSpan (I := I) P F b) :
          Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b)) := by
      have := (Submodule.subtypeL (r26t8a_progSpan (I := I) P F b)).integral_comp_comm
        (hVint.mono_set hsub)
      simpa using this.symm
    apply Subtype.ext
    change embL2 (hH t ht) b = embL2 (hH 0 h0) b +
      (((∫ v in Icc 0 t, V v) : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))
    rw [hint]
    have hGm : AEStronglyMeasurable (Function.uncurry fun (v : ℝ) (q : ℝ × Omega) =>
        (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) q.1 q.2) : EuclideanSpace ℝ I))
        ((volume.restrict (Icc 0 t)).prod (tsMeasure P b)) :=
      (r26t8a_s02_joint P b 0 T (fun v => r26t8a_clipIntegrand a b (Hd v)) hm').mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
    have hVG : ∀ᵐ v ∂(volume.restrict (Icc 0 t)), ⇑((V v : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b)) =ᵐ[tsMeasure P b]
        fun q : ℝ × Omega => (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) q.1 q.2) :
          EuclideanSpace ℝ I) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [hVeq v (hsub hv)]
      exact r26t8a_s02_coe_ae P F b 0 T (fun v => r26t8a_clipIntegrand a b (Hd v)) hHd v (hsub hv)
    have hL := r26t8a_s04a_integral_ae (volume.restrict (Icc 0 t)) (tsMeasure P b)
      (fun v => ((V v : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))) hVct
      (fun v q => (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) q.1 q.2) :
        EuclideanSpace ℝ I)) hGm hVG
    have hF' : ∀ᵐ q ∂(tsMeasure P b),
        (WithLp.toLp 2 (r26t8a_clipIntegrand a b (H t) q.1 q.2) : EuclideanSpace ℝ I) =
        WithLp.toLp 2 (r26t8a_clipIntegrand a b (H 0) q.1 q.2) +
          ∫ v in Icc 0 t,
            (WithLp.toLp 2 (r26t8a_clipIntegrand a b (Hd v) q.1 q.2) : EuclideanSpace ℝ I) := by
      filter_upwards [hgood] with q hq
      exact r26t8a_s04_pointwise a b T t ht H Hd q.1 q.2 hq
    have cT := r26t8a_s02_coe_ae P F b 0 T (fun t => r26t8a_clipIntegrand a b (H t)) hH t ht
    have c0 := r26t8a_s02_coe_ae P F b 0 T (fun t => r26t8a_clipIntegrand a b (H t)) hH 0 h0
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (embL2 (hH 0 h0) b)
      (∫ v in Icc 0 t, ((V v : r26t8a_progSpan (I := I) P F b) :
        Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))), cT, c0, hL, hF'] with q h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, h4]
    exact h5

end HRS.MS.R26T8A

end
