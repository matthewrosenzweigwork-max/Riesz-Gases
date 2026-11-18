import HRS.MS.R26T8AS01
import HRS.MS.R26T8AS03
import HRS.MS.R26T8AS06
import HRS.MS.R26T8AS07a
import HRS.MS.R26T8AS07b
import HRS.MS.R26T8AB00m

/-!
# S8.2 observed-time layer, packet T8A.S07: recent-past Itô integral with parameter, Fubini form

Route: S06 gives the triangular FTC in `progSpan` at horizon `a+T`; the Itô map `J` of S01 transports it; S03 gives a
jointly measurable representative `Jd` of `v ↦ J (V v)`; the link lemma `r26t8a_s04a_integral_ae` identifies
`∫_{[a,t]} J (V v) dv` with the pointwise integral of `Jd`; locality of the integral of clipped integrands
(`r26t8a_s07b_local`) moves the horizon `a+T` to the variable endpoint; `G` is the continuous diagonal martingale
plus the primitive on the good event (`r26t8a_s07a_prim`); Doob's `L²` inequality and Minkowski give the bound.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_s07_embed_enorm {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ)
    (H : ℝ → Omega → I → ℝ) (hH : IsProgressiveL2 P F H) :
    ‖r26t8a_progEmbed P F b H hH‖ₑ ^ 2 = sqIntegralOn P H b := by
  have h1 : ‖r26t8a_progEmbed P F b H hH‖ = ‖embL2 hH b‖ := Submodule.coe_norm _
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1, norm_embL2_sq,
    ENNReal.ofReal_toReal (hH.sq b).ne]

theorem r26t8a_s07_clip_idem {Omega I : Type*} (a v : ℝ) (G : ℝ → Omega → I → ℝ) :
    r26t8a_clipIntegrand a v (r26t8a_clipIntegrand a v G) = r26t8a_clipIntegrand a v G := by
  funext r w i
  by_cases h : r ∈ Icc a v <;> simp [r26t8a_clipIntegrand, h]

theorem r26t8a_recent_ito_fubini
    {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 < T)
    (H Hd : ℝ → ℝ → Omega → I → ℝ)
    (hdiag : IsProgressiveL2 P F (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)))
    (hH : ∀ t ∈ Set.Icc a (a + T), IsProgressiveL2 P F (r26t8a_clipIntegrand a t (H t)))
    (hHd : ∀ t ∈ Set.Icc a (a + T), IsProgressiveL2 P F (r26t8a_clipIntegrand a t (Hd t)))
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega =>
      if p.1.2 ≤ p.1.1 then Hd p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc a (a + T))).prod
        (volume.restrict (Set.Icc a (a + T)))).prod P))
    (he : (∫⁻ v in Set.Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v) < ⊤)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc a (a + T))).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc p.1 (a + T)) ∧
      ∀ t ∈ Set.Icc p.1 (a + T),
        H t p.1 p.2 i = H p.1 p.1 p.2 i + ∫ v in Set.Icc p.1 t, Hd v p.1 p.2 i) :
    ∃ G J : ℝ → Omega → ℝ,
      Measurable (Function.uncurry G) ∧ Measurable (Function.uncurry J) ∧
      (∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T)) ∧
      (∀ t ∈ Set.Icc 0 T,
        G t =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a (a + t) (H (a + t))) (a + t)) ∧
      (∀ᵐ v ∂volume.restrict (Set.Icc a (a + T)),
        J v =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a v (Hd v)) v) ∧
      (∀ᵐ w ∂P, ∀ t ∈ Set.Icc 0 T,
        G t w = itoIntegral P F W
          (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) (a + t) w +
            ∫ v in Set.Icc a (a + t), J v w) ∧
      r26t8a_scalarSupSq P T G ≤
        8 * r26t8a_itoEnergy P (fun r w i => H r r w i) a (a + T) +
          ENNReal.ofReal (2 * T) * ∫⁻ v in Set.Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v := by
  classical
  have hb : 0 ≤ a + T := by linarith
  haveI hcs : CompleteSpace (r26t8a_progSpan (I := I) P F (a + T)) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨V, hVint, hVeq, hVt⟩ := r26t8a_triangle_FTC P F a T ha hT H Hd hdiag hH hHd hm he hFTC
  obtain ⟨J, hJ1, hJeq⟩ := r26t8a_ito_continuousLinear P F W hW (a + T) hb
  have hJle : ∀ x, ‖J x‖ₑ ≤ ‖x‖ₑ := by
    intro x
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((J.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hJ1))
  have hVen : ∀ v ∈ Icc a (a + T), ‖V v‖ₑ ^ 2 = r26t8a_itoEnergy P (Hd v) a v := by
    intro v hv
    rw [hVeq v hv, r26t8a_s07_embed_enorm, r26t8a_s06_sq_clip P a v (a + T) ha hv.2]
  have hUae : AEStronglyMeasurable (fun v => J (V v)) (volume.restrict (Icc a (a + T))) :=
    J.continuous.comp_aestronglyMeasurable hVint.1
  have hUle : ∀ v ∈ Icc a (a + T), ‖J (V v)‖ₑ ^ 2 ≤ r26t8a_itoEnergy P (Hd v) a v := by
    intro v hv
    calc ‖J (V v)‖ₑ ^ 2 ≤ ‖V v‖ₑ ^ 2 := by gcongr; exact hJle _
      _ = _ := hVen v hv
  have hUen : (∫⁻ v in Icc a (a + T), ‖J (V v)‖ₑ ^ 2) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hUle) he
  obtain ⟨Jd, hJdm, hJdae, hJdL2, hJdnorm⟩ :=
    r26t8a_joint_representative P a (a + T) (by linarith) (fun v => J (V v)) hUae hUen
  -- the diagonal martingale
  have hMc : ∀ w, Continuous fun t => itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w :=
    continuous_itoIntegral P F W _
  have hMm : ∀ t, Measurable (itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t) := fun t =>
    (adapted_itoIntegral P F W _ t).mono (F.le t) le_rfl
  have hint1 : Integrable (Function.uncurry Jd) ((volume.restrict (Icc a (a + T))).prod P) :=
    hJdL2.integrable one_le_two
  have hsec : ∀ᵐ w ∂P, Integrable (fun v => Jd v w) (volume.restrict (Icc a (a + T))) :=
    hint1.prod_left_ae
  have hgood : ∀ᵐ w ∂P, (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ⊤ := by
    filter_upwards [hsec] with w hw
    exact hw.hasFiniteIntegral
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Omega → ℝ, G = r26t8a_s07a_prim (itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i))) Jd a T := ⟨_, rfl⟩
  have hGm : Measurable (Function.uncurry G) := by
    subst hGdef; exact r26t8a_s07a_meas _ hMc hMm Jd hJdm a T
  have hGc : ∀ w, ContinuousOn (fun t => G t w) (Icc 0 T) := by
    subst hGdef; exact r26t8a_s07a_cont _ hMc Jd hJdm a T
  have hGftc : ∀ w, (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ⊤ → ∀ t,
      G t w = itoIntegral P F W (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) (a + t) w +
        ∫ v in Icc a (a + t), Jd v w := by
    intro w hw t; subst hGdef; exact r26t8a_s07a_ftc _ Jd a T w hw t
  have hM0 : ∀ᵐ w ∂P, itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) a w = 0 :=
    r26t8a_s07b_zero P F W hW (fun r w i => H r r w i) a (a + T) hdiag
  -- (iv) the derivative representative
  have hItem5 : ∀ᵐ v ∂(volume.restrict (Icc a (a + T))),
      Jd v =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a v (Hd v)) v := by
    filter_upwards [hJdae, ae_restrict_mem measurableSet_Icc] with v h1 hv
    refine h1.trans ?_
    have h2 : J (V v) = (memLp_two_itoIntegral hW (hHd v hv) (a + T)).toLp
        (itoIntegral P F W (r26t8a_clipIntegrand a v (Hd v)) (a + T)) := by
      rw [hVeq v hv]
      exact hJeq _ _
    have hcl : IsProgressiveL2 P F
        (r26t8a_clipIntegrand a v (r26t8a_clipIntegrand a v (Hd v))) := by
      rw [r26t8a_s07_clip_idem]; exact hHd v hv
    have hloc := r26t8a_s07b_local P F W hW _ (hHd v hv) a v ha hv.1 hcl
    rw [r26t8a_s07_clip_idem] at hloc
    have hcoe := (memLp_two_itoIntegral hW (hHd v hv) (a + T)).coeFn_toLp
    rw [h2]
    filter_upwards [hcoe, hloc] with w a1 a2
    have e1 := a2 (a + T)
    have e2 := a2 v
    have m1 : min (a + T) v = v := min_eq_right hv.2
    have m2 : min (a + T) a = a := min_eq_right (by linarith)
    have m3 : min v v = v := min_self v
    have m4 : min v a = a := min_eq_right hv.1
    rw [m1, m2] at e1
    rw [m3, m4] at e2
    rw [a1]
    linarith
  -- (iii) identification at each time
  have hItem4 : ∀ t ∈ Icc 0 T, G t =ᵐ[P]
      itoIntegral P F W (r26t8a_clipIntegrand a (a + t) (H (a + t))) (a + t) := by
    intro t ht
    have ht' : a + t ∈ Icc a (a + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hDt, hid⟩ := hVt (a + t) ht'
    have hsub : Icc a (a + t) ⊆ Icc a (a + T) := Icc_subset_Icc_right (by linarith [ht.2])
    have hVt' : Integrable V (volume.restrict (Icc a (a + t))) := hVint.mono_set hsub
    have h1 := congrArg J hid
    rw [map_add, hJeq, hJeq, ← J.integral_comp_comm hVt'] at h1
    have hVG : ∀ᵐ v ∂(volume.restrict (Icc a (a + t))), ⇑(J (V v)) =ᵐ[P] Jd v := by
      have := hJdae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
      filter_upwards [this] with v hv
      exact hv.symm
    have hL := r26t8a_s04a_integral_ae (volume.restrict (Icc a (a + t))) P (fun v => J (V v))
      (J.integrable_comp hVt') Jd hJdm.aestronglyMeasurable hVG
    have h3 := congrFun (congrArg (fun x : Lp ℝ 2 P => (x : Omega → ℝ)) h1)
    have hclH : IsProgressiveL2 P F
        (r26t8a_clipIntegrand a (a + t) (r26t8a_clipIntegrand a (a + t) (H (a + t)))) := by
      rw [r26t8a_s07_clip_idem]; exact hH (a + t) ht'
    have hlocH := r26t8a_s07b_local P F W hW _ (hH (a + t) ht') a (a + t) ha
      (by linarith [ht.1]) hclH
    rw [r26t8a_s07_clip_idem] at hlocH
    have eDD : r26t8a_clipIntegrand a (a + t)
        (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) =
        r26t8a_clipIntegrand a (a + t) (fun r w i => H r r w i) := by
      funext r w i
      by_cases h : r ∈ Icc a (a + t)
      · have : r ∈ Icc a (a + T) := ⟨h.1, h.2.trans (by linarith [ht.2])⟩
        simp [r26t8a_clipIntegrand, h, this]
      · simp [r26t8a_clipIntegrand, h]
    have hDD : IsProgressiveL2 P F (r26t8a_clipIntegrand a (a + t)
        (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i))) := by
      rw [eDD]; exact hDt
    have hlocD := r26t8a_s07b_local P F W hW _ hdiag a (a + t) ha (by linarith [ht.1]) hDD
    rw [eDD] at hlocD
    filter_upwards [(memLp_two_itoIntegral hW (hH (a + t) ht') (a + T)).coeFn_toLp,
      (memLp_two_itoIntegral hW hDt (a + T)).coeFn_toLp,
      Lp.coeFn_add ((memLp_two_itoIntegral hW hDt (a + T)).toLp
        (itoIntegral P F W (r26t8a_clipIntegrand a (a + t) (fun r w i => H r r w i)) (a + T)))
        (∫ v in Icc a (a + t), J (V v)), hL, hgood, hlocH, hlocD, hM0] with w a1 a2 a3 a4 a5 a6 a7 a8
    have m1 : min (a + T) (a + t) = a + t := min_eq_right (by linarith [ht.2])
    have m2 : min (a + t) (a + t) = a + t := min_self _
    have m3 : min (a + T) a = a := min_eq_right (by linarith)
    have m4 : min (a + t) a = a := min_eq_right (by linarith [ht.1])
    have e1 := a6 (a + T)
    have e2 := a6 (a + t)
    have f1 := a7 (a + T)
    rw [m1, m3] at e1
    rw [m2, m4] at e2
    rw [m1, m3] at f1
    have h4 := h3 w
    rw [a1] at h4
    have k1 : itoIntegral P F W (r26t8a_clipIntegrand a (a + t) (H (a + t))) (a + T) w =
        itoIntegral P F W (r26t8a_clipIntegrand a (a + t) (fun r w i => H r r w i)) (a + T) w +
          ∫ v in Icc a (a + t), Jd v w := by
      rw [h4, a3, Pi.add_apply, a2, a4]
    rw [hGftc w a5 t]
    linarith [k1, e1, e2, f1, a8]
  -- (vi) the formula on the good event
  have hItem6 : ∀ᵐ w ∂P, ∀ t ∈ Icc 0 T, G t w = itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) (a + t) w +
        ∫ v in Icc a (a + t), Jd v w := by
    filter_upwards [hgood] with w hw t _
    exact hGftc w hw t
  -- (vii) the supremum bound
  have hBm : Measurable fun w => ∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ :=
    Measurable.lintegral_prod_left' (f := fun p : ℝ × Omega => ‖Jd p.1 p.2‖ₑ) hJdm.enorm
  have hpt : ∀ w, (⨆ t : Icc (0 : ℝ) T, ‖G t w‖ₑ) ^ 2 ≤
      2 * ((⨆ t ∈ Icc (0 : ℝ) (a + T), ‖itoIntegral P F W
        (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w‖ₑ) ^ 2 +
        (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) ^ 2) := by
    intro w
    by_cases hw : (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ⊤
    · set A := ⨆ t ∈ Icc (0 : ℝ) (a + T), ‖itoIntegral P F W
        (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w‖ₑ with hA
      set B := ∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ with hB
      have hle : (⨆ t : Icc (0 : ℝ) T, ‖G t w‖ₑ) ≤ A + B := by
        refine iSup_le fun t => ?_
        rw [hGftc w hw t]
        calc _ ≤ ‖itoIntegral P F W
              (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) (a + (t : ℝ)) w‖ₑ +
              ‖∫ v in Icc a (a + (t : ℝ)), Jd v w‖ₑ := enorm_add_le _ _
          _ ≤ A + B := by
            refine add_le_add ?_ ?_
            · refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ) (_ : t' ∈ Icc (0 : ℝ) (a + T)) =>
                ‖itoIntegral P F W
                  (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t' w‖ₑ)
                (a + (t : ℝ)) ⟨by linarith [t.2.1], by linarith [t.2.2]⟩)
              exact le_rfl
            · refine (enorm_integral_le_lintegral_enorm _).trans ?_
              exact lintegral_mono_set (Icc_subset_Icc_right (by linarith [t.2.2]))
      have hsq := ENNReal.rpow_add_le_mul_rpow_add_rpow A B (p := 2) (by norm_num)
      simp only [ENNReal.rpow_two] at hsq
      have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
      rw [h2] at hsq
      exact (pow_le_pow_left' hle 2).trans hsq
    · have hz : ∀ t, G t w = 0 := by
        intro t; subst hGdef; simp [r26t8a_s07a_prim, hw]
      simp [hz]
  have hb1 : ∫⁻ w, (⨆ t ∈ Icc (0 : ℝ) (a + T), ‖itoIntegral P F W
      (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w‖ₑ) ^ 2 ∂P ≤
      4 * r26t8a_itoEnergy P (fun r w i => H r r w i) a (a + T) := by
    refine (lintegral_iSup_itoIntegral_sq_le hW hdiag (a + T)).trans (le_of_eq ?_)
    rw [r26t8a_s06_sq_clip P a (a + T) (a + T) ha le_rfl]
  have hb2 : ∫⁻ w, (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal T * ∫⁻ v in Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v := by
    have hF : Measurable (Function.uncurry fun (w : Omega) (r : ℝ) => ‖Jd r w‖ₑ) :=
      hJdm.enorm.comp measurable_swap
    have hk := r26t8a_minkowski_sq P a (a + T) hF
    simp only [ENNReal.rpow_two] at hk
    rw [Real.volume_Icc, show a + T - a = T by ring] at hk
    refine hk.trans (mul_le_mul' le_rfl ?_)
    have h5 : ∫⁻ p, ‖Jd p.1 p.2‖ₑ ^ 2 ∂((volume.restrict (Icc a (a + T))).prod P) =
        ∫⁻ v in Icc a (a + T), ∫⁻ w, ‖Jd v w‖ₑ ^ 2 ∂P :=
      lintegral_prod _ ((hJdm.enorm.pow_const 2).aemeasurable)
    rw [← h5, hJdnorm]
    exact setLIntegral_mono' measurableSet_Icc hUle
  refine ⟨G, Jd, hGm, hJdm, hGc, hItem4, hItem5, hItem6, ?_⟩
  have hsup : r26t8a_scalarSupSq P T G ≤ ∫⁻ w, 2 * ((⨆ t ∈ Icc (0 : ℝ) (a + T), ‖itoIntegral P F W
        (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w‖ₑ) ^ 2 +
        (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) ^ 2) ∂P :=
    lintegral_mono hpt
  refine hsup.trans ?_
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ (hBm.pow_const 2)]
  have h2T : ENNReal.ofReal (2 * T) = 2 * ENNReal.ofReal T := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h2T]
  calc 2 * (∫⁻ w, (⨆ t ∈ Icc (0 : ℝ) (a + T), ‖itoIntegral P F W
          (r26t8a_clipIntegrand a (a + T) (fun r w i => H r r w i)) t w‖ₑ) ^ 2 ∂P +
        ∫⁻ w, (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) ^ 2 ∂P)
      ≤ 2 * (4 * r26t8a_itoEnergy P (fun r w i => H r r w i) a (a + T) +
        ENNReal.ofReal T * ∫⁻ v in Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v) := by
        gcongr
    _ = 8 * r26t8a_itoEnergy P (fun r w i => H r r w i) a (a + T) +
        2 * ENNReal.ofReal T * ∫⁻ v in Icc a (a + T), r26t8a_itoEnergy P (Hd v) a v := by
        ring

end HRS.MS.R26T8A

end
