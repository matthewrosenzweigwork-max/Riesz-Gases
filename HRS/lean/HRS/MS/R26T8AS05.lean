import HRS.MS.CritForceObs1
import HRS.MS.R26T8AS01
import HRS.MS.R26T8AS03
import HRS.MS.R26T8AS04
import HRS.MS.R26T8AS05a

/-!
# S8.2 observed-time layer, packet T8A.S05: Itô integrals of a parameter family on a fixed interval

Route: S04 gives the `progSpan`-valued derivative `V` and the Bochner FTC for the embeddings; the continuous linear
Itô map `J` of S01 transports both; S03 gives a jointly measurable representative `Gd` of `t ↦ J (V t)`; the link lemma
`r26t8a_s04a_integral_ae` identifies `∫ J (V v) dv` with the pointwise integral of `Gd`; `G` is the primitive
`r26t8a_s05a_prim` (initial value plus parameter integral on the good event, zero elsewhere), and the anchored
supremum bound `s82n_anchored_observed_sup` gives the stated estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_s05_embed_enorm {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ)
    (H : ℝ → Omega → I → ℝ) (hH : IsProgressiveL2 P F H) :
    ‖r26t8a_progEmbed P F b H hH‖ₑ ^ 2 = sqIntegralOn P H b := by
  have h1 : ‖r26t8a_progEmbed P F b H hH‖ = ‖embL2 hH b‖ := Submodule.coe_norm _
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1, norm_embL2_sq,
    ENNReal.ofReal_toReal (hH.sq b).ne]

theorem r26t8a_fixed_interval_ito_parameter
    {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W)
    (a b T : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 < T)
    (H Hd : ℝ → ℝ → Omega → I → ℝ)
    (hH : ∀ t ∈ Set.Icc 0 T, IsProgressiveL2 P F (r26t8a_clipIntegrand a b (H t)))
    (hHd : ∀ t ∈ Set.Icc 0 T, IsProgressiveL2 P F (r26t8a_clipIntegrand a b (Hd t)))
    (hm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × Omega => Hd p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc a b))).prod P))
    (he : (∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) a b) < ⊤)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod P), ∀ i,
      IntegrableOn (fun t => Hd t p.1 p.2 i) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T,
        H t p.1 p.2 i = H 0 p.1 p.2 i + ∫ v in Set.Icc 0 t, Hd v p.1 p.2 i) :
    ∃ G Gd : ℝ → Omega → ℝ,
      Measurable (Function.uncurry G) ∧ Measurable (Function.uncurry Gd) ∧
      (∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T)) ∧
      (∀ t ∈ Set.Icc 0 T,
        G t =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (H t)) b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        Gd t =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (Hd t)) b) ∧
      (∀ᵐ w ∂P, ∀ t ∈ Set.Icc 0 T,
        G t w = G 0 w + ∫ v in Set.Icc 0 t, Gd v w) ∧
      r26t8a_scalarSupSq P T G ≤
        2 * r26t8a_itoEnergy P (H 0) a b +
          ENNReal.ofReal (2 * T) * ∫⁻ t in Set.Icc 0 T, r26t8a_itoEnergy P (Hd t) a b := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  haveI hcs : CompleteSpace (r26t8a_progSpan (I := I) P F b) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨V, hVint, hVeq, hFTCe⟩ :=
    r26t8a_integrand_FTC P F a b T ha hab hT H Hd hH hHd hm he hFTC
  obtain ⟨J, hJ1, hJeq⟩ := r26t8a_ito_continuousLinear P F W hW b hb
  have hJle : ∀ x, ‖J x‖ₑ ≤ ‖x‖ₑ := by
    intro x
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((J.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hJ1))
  have hVen : ∀ t ∈ Icc 0 T, ‖V t‖ₑ ^ 2 = r26t8a_itoEnergy P (Hd t) a b := by
    intro t ht
    rw [hVeq t ht, r26t8a_s05_embed_enorm, r26t8a_s04_sq_clip P a b ha hab]
  have hUae : AEStronglyMeasurable (fun t => J (V t)) (volume.restrict (Icc 0 T)) :=
    J.continuous.comp_aestronglyMeasurable hVint.1
  have hUle : ∀ t ∈ Icc 0 T, ‖J (V t)‖ₑ ^ 2 ≤ r26t8a_itoEnergy P (Hd t) a b := by
    intro t ht
    calc ‖J (V t)‖ₑ ^ 2 ≤ ‖V t‖ₑ ^ 2 := by gcongr; exact hJle _
      _ = _ := hVen t ht
  have hUen : (∫⁻ t in Icc 0 T, ‖J (V t)‖ₑ ^ 2) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc hUle) he
  obtain ⟨Gd, hGdm, hGdae, hGdL2, hGdnorm⟩ :=
    r26t8a_joint_representative P 0 T hT.le (fun t => J (V t)) hUae hUen
  have hmem0 := memLp_two_itoIntegral hW (hH 0 hT0) b
  let G0 : Omega → ℝ := AEStronglyMeasurable.mk
    (itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b) hmem0.aestronglyMeasurable
  have hG0m : Measurable G0 := hmem0.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hG0ae : G0 =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b :=
    hmem0.aestronglyMeasurable.ae_eq_mk.symm
  have hint1 : Integrable (Function.uncurry Gd) ((volume.restrict (Icc 0 T)).prod P) :=
    hGdL2.integrable one_le_two
  have hsec : ∀ᵐ w ∂P, Integrable (fun v => Gd v w) (volume.restrict (Icc 0 T)) :=
    hint1.prod_left_ae
  have hgood : ∀ᵐ w ∂P, (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ⊤ := by
    filter_upwards [hsec] with w hw
    exact hw.hasFiniteIntegral
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Omega → ℝ, G = r26t8a_s05a_prim G0 Gd T := ⟨_, rfl⟩
  have hGm : Measurable (Function.uncurry G) := by
    subst hGdef; exact r26t8a_s05a_meas G0 hG0m Gd hGdm T
  have hGc : ∀ w, ContinuousOn (fun t => G t w) (Icc 0 T) := by
    subst hGdef; exact r26t8a_s05a_cont G0 Gd hGdm T
  have hGzero : ∀ w, (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ⊤ → G 0 w = G0 w := by
    intro w hw; subst hGdef; exact r26t8a_s05a_zero G0 Gd T w hw
  have hGftc : ∀ w, (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ⊤ → ∀ t,
      G t w = G0 w + ∫ v in Icc 0 t, Gd v w := by
    intro w hw t; subst hGdef; exact r26t8a_s05a_ftc G0 Gd T w hw t
  have hG0eq : ∀ᵐ w ∂P, G 0 w = itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b w := by
    filter_upwards [hgood, hG0ae] with w hw h6
    rw [hGzero w hw, h6]
  have hItem4 : ∀ t ∈ Icc 0 T,
      G t =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (H t)) b := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hVt : Integrable V (volume.restrict (Icc 0 t)) := hVint.mono_set hsub
    have h1 := congrArg J (hFTCe t ht)
    rw [map_add, hJeq, hJeq, ← J.integral_comp_comm hVt] at h1
    have hVG : ∀ᵐ v ∂(volume.restrict (Icc 0 t)), ⇑(J (V v)) =ᵐ[P] Gd v := by
      have := hGdae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
      filter_upwards [this] with v hv
      exact hv.symm
    have hL := r26t8a_s04a_integral_ae (volume.restrict (Icc 0 t)) P (fun v => J (V v))
      (J.integrable_comp hVt) Gd hGdm.aestronglyMeasurable hVG
    have h3 := congrFun (congrArg (fun x : Lp ℝ 2 P => (x : Omega → ℝ)) h1)
    filter_upwards [(memLp_two_itoIntegral hW (hH t ht) b).coeFn_toLp, hmem0.coeFn_toLp,
      Lp.coeFn_add ((memLp_two_itoIntegral hW (hH 0 hT0) b).toLp
        (itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b))
        (∫ v in Icc 0 t, J (V v)), hL, hgood, hG0ae] with w a1 a2 a3 a4 a5 a6
    have e1 : itoIntegral P F W (r26t8a_clipIntegrand a b (H t)) b w =
        itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b w + ∫ v in Icc 0 t, Gd v w := by
      rw [← a1, h3 w, a3, Pi.add_apply, a2, a4]
    rw [hGftc w a5 t, a6, e1]
  have hItem5 : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      Gd t =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (Hd t)) b := by
    filter_upwards [hGdae, ae_restrict_mem measurableSet_Icc] with t h1 ht
    refine h1.trans ?_
    have h2 : J (V t) = (memLp_two_itoIntegral hW (hHd t ht) b).toLp
        (itoIntegral P F W (r26t8a_clipIntegrand a b (Hd t)) b) := by
      rw [hVeq t ht]
      exact hJeq _ _
    rw [h2]
    exact MemLp.coeFn_toLp _
  have hItem6 : ∀ᵐ w ∂P, ∀ t ∈ Icc 0 T, G t w = G 0 w + ∫ v in Icc 0 t, Gd v w := by
    filter_upwards [hgood] with w hw t ht
    rw [hGftc w hw t, hGzero w hw]
  have hG0eq' : G 0 =ᵐ[P] itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b := hG0eq
  have hY0 : MemLp (G 0) 2 P := MemLp.ae_eq hG0eq'.symm hmem0
  have hFTC' : ∀ᵐ w ∂P, IntegrableOn (fun t => Gd t w) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, G t w = G 0 w + ∫ r in Icc 0 t, Gd r w := by
    filter_upwards [hsec, hItem6] with w h1 h2
    exact ⟨h1, h2⟩
  have hsup := (HRS.MS.S82N.s82n_anchored_observed_sup P T hT G Gd hY0 hGdL2 hFTC').2
  have hb1 : ∫⁻ w, ‖G 0 w‖ₑ ^ 2 ∂P ≤ r26t8a_itoEnergy P (H 0) a b := by
    have e1 : ∫⁻ w, ‖G 0 w‖ₑ ^ 2 ∂P =
        ∫⁻ w, ‖itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b w‖ₑ ^ 2 ∂P :=
      lintegral_congr_ae (hG0eq.mono fun w h => by simp only [h])
    have e2 : ∫⁻ w, ‖itoIntegral P F W (r26t8a_clipIntegrand a b (H 0)) b w‖ₑ ^ 2 ∂P =
        ‖J (r26t8a_progEmbed P F b (r26t8a_clipIntegrand a b (H 0)) (hH 0 hT0))‖ₑ ^ 2 := by
      rw [hJeq, Lp.enorm_def, ← HRS.lintegral_enorm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable _)]
      refine lintegral_congr_ae ?_
      filter_upwards [hmem0.coeFn_toLp] with w hw
      rw [hw]
    rw [e1, e2, ← r26t8a_s04_sq_clip P a b ha hab, ← r26t8a_s05_embed_enorm P F b _ (hH 0 hT0)]
    gcongr
    exact hJle _
  have hb2 : ∫⁻ p, ‖Gd p.1 p.2‖ₑ ^ 2 ∂((volume.restrict (Icc 0 T)).prod P) ≤
      ∫⁻ t in Icc 0 T, r26t8a_itoEnergy P (Hd t) a b := by
    rw [hGdnorm]
    exact setLIntegral_mono' measurableSet_Icc hUle
  refine ⟨G, Gd, hGm, hGdm, hGc, hItem4, hItem5, hItem6, ?_⟩
  exact hsup.trans (by gcongr)

end HRS.MS.R26T8A

end
