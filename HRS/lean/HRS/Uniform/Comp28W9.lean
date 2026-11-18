import HRS.Uniform.Comp28W8
import HRS.Uniform.Comp28Aux4

/-!
# COMP-28, Wasserstein part, W9: uniqueness in law of the Gaussian convolution (transfer to an enlargement)

Given a Hilbert martingale `G` on `(Ω, ℱ)` with a stochastic convolution `Zb` and a second Hilbert martingale `Gb` on
`(Ω', ℱ')` with the same covariation density on `[0,T]`, there is a continuous convolution `Z'` of `Gb` such that
`V(·,0)ξ' + Z'` has on `Ω'` the law of `V(·,0)ξ + Zb` on `Ω`, for `ℱ_0`-measurable vectors `ξ, ξ'` of the same law.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q07c HRS.GF

section Transfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma continuous_vpathW (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {B : ℝ} (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖V t 0‖ ≤ B) : Continuous (vpathW V hc) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨B, hB0⟩) fun x x' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  refine norm_pcm_le _ (mul_nonneg hB0 (norm_nonneg _)) fun t => ?_
  rw [pcm_sub, pcm_vpathW, pcm_vpathW, ← map_sub]
  exact ((V _ 0).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB t t.2) (norm_nonneg _))

lemma windowPath_vadd {Ω : Type*} (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ}
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (x : Ω → H) (Y : ℝ → Ω → H) {ω : Ω} (hY : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    windowPath 0 T (fun t ω => V t 0 (x ω) + Y t ω) ω = vpathW V hc (x ω) + windowPath 0 T Y ω := by
  have h1 : ContinuousOn (fun t => V t 0 (x ω) + Y t ω) (Set.Icc 0 T) :=
    (continuousOn_V_zero V hc (x ω)).add hY
  refine pcm_ext fun t => ?_
  rw [pcm_windowPath _ h1, pcm_add, pcm_vpathW, pcm_windowPath Y hY]

/-- `IsStochConv` only depends on `G` up to a.e. modification at the times in `[0,t]` (copy of
`HRS.GF.gfb4_isStochConv_congr`). -/
theorem isStochConv_congr_times {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (VE : ℝ → ℝ → H →L[ℝ] H) (j : H →L[ℝ] H) {G G' : ℝ → Ω → H} {t : ℝ} (ht : 0 ≤ t)
    (hGG : ∀ τ ∈ Set.Icc (0 : ℝ) t, G' τ =ᵐ[P] G τ) {Z : Ω → H}
    (h : IsStochConv P VE j G 0 t Z) : IsStochConv P VE j G' 0 t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have hmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) t := fun i => by
    refine ⟨h0 ▸ hmono (Fin.zero_le i), hn ▸ hmono (Fin.le_last i)⟩
  have hae : ∀ᵐ ω ∂P, ∀ i, G' (r i) ω = G (r i) ω := ae_all_iff.2 fun i => hGG _ (hmem i)
  refine lt_of_le_of_lt (le_of_eq ?_) (hh n r h0 hn hmono hmesh)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ω hω
  simp only [riemannSum, hω]


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Uniqueness in law of the Gaussian convolution.** -/
theorem transfer_conv {ℱ : Filtration ℝ mΩ} {ℱ' : Filtration ℝ mΩ'} {G : ℝ → Ω → H} {Gb : ℝ → Ω' → H}
    {d d₂ : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => d r))
    (hGb : IsHilbertMartingaleWithCovariation P' ℱ' T Gb (fun r _ => d₂ r))
    (hd : ∀ r ∈ Set.Icc (0 : ℝ) T, d₂ r = d r) (V : ℝ → ℝ → H →L[ℝ] H)
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {B : ℝ} (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖V t 0‖ ≤ B)
    {Zb : ℝ → Ω → H} (hZm : ∀ t, Measurable (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    {ξ : Ω → H} {ξ' : Ω' → H} (hξ : Measurable[ℱ 0] ξ) (hξ' : Measurable[ℱ' 0] ξ')
    (hlaw : P.map ξ = P'.map ξ') :
    ∃ Z' : ℝ → Ω' → H, (∀ t, Measurable (Z' t)) ∧
      (∀ ω', ContinuousOn (fun t => Z' t ω') (Set.Icc 0 T)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' V (ContinuousLinearMap.id ℝ H) Gb 0 t (Z' t)) ∧
      law P (windowPath 0 T (fun t ω => V t 0 (ξ ω) + Zb t ω)) =
        law P' (windowPath 0 T (fun t ω' => V t 0 (ξ' ω') + Z' t ω')) := by
  classical
  obtain ⟨Gt, hGt, hct, hzt, hGG⟩ := modify_HM hT hG
  obtain ⟨Gtb, hGtb, hctb, hztb, hGGb⟩ := modify_HM hT hGb
  have hdh : dhat d₂ T = dhat d T := by
    funext r
    by_cases h : r ∈ Set.Icc (0 : ℝ) T
    · rw [dhat_of_mem d₂ T h, dhat_of_mem d T h, hd r h]
    · rw [dhat_zero d₂ T h, dhat_zero d T h]
  rw [hdh] at hGtb
  have hGm : ∀ t, Measurable (Gt t) := fun t => measurable_of_isHM hGt t
  have hGmb : ∀ t, Measurable (Gtb t) := fun t => measurable_of_isHM hGtb t
  have hZt : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V (ContinuousLinearMap.id ℝ H) Gt 0 t (Zb t) :=
    fun t ht => isStochConv_congr_times P V (ContinuousLinearMap.id ℝ H) ht.1
      (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZ t ht)
  obtain ⟨h, hhm, hhae⟩ := exists_path_funct hT hGm hct hZm hZc hZt
  -- measurability of the path maps
  have hsup : (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ T}, MeasurableSpace.comap (Gt τ) inferInstance) ≤ mΩ :=
    iSup₂_le fun τ _ => (hGm τ).comap_le
  have hsupb : (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ T}, MeasurableSpace.comap (Gtb τ) inferInstance) ≤ mΩ' :=
    iSup₂_le fun τ _ => (hGmb τ).comap_le
  have hpm : Measurable (windowPath 0 T Gt) := (measurable_path_sup hT hct).mono hsup le_rfl
  have hpmb : Measurable (windowPath 0 T Gtb) := (measurable_path_sup hT hctb).mono hsupb le_rfl
  -- the new convolution
  set Z' : ℝ → Ω' → H := fun t ω' => pcm (h (windowPath 0 T Gtb ω')) (Set.projIcc 0 T hT t) with hZ'
  have hZ'c : ∀ ω', Continuous fun t => Z' t ω' := fun ω' =>
    (pcm (h (windowPath 0 T Gtb ω'))).continuous.comp (continuous_projIcc (h := hT))
  have hZ'm : ∀ t, Measurable (Z' t) := fun t =>
    (continuous_eval_const (Set.projIcc 0 T hT t) : Continuous fun y : C(Set.Icc (0 : ℝ) T, H) =>
      y (Set.projIcc 0 T hT t)).measurable.comp (hhm.comp hpmb)
  -- law of the paths
  have hpathlaw : law P (windowPath 0 T Gt) = law P' (windowPath 0 T Gtb) :=
    law_path_eq_of_fdd hT P P' Gt Gtb hGm hGmb (Filter.Eventually.of_forall fun ω => (hct ω).continuousOn)
      (Filter.Eventually.of_forall fun ω => (hctb ω).continuousOn)
      (fun p ts hts => law_fdd_eq_G hT hGt hGtb hct hzt hctb hztb ts hts)
  have hZbh : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Zb t ω = pcm (h (windowPath 0 T Gt ω)) (Set.projIcc 0 T hT t) := by
    filter_upwards [hhae, hZc] with ω h1 h2 t ht
    rw [← h1, pcm_windowPath Zb h2, Set.projIcc_of_mem hT ht]
  refine ⟨Z', hZ'm, fun ω' => (hZ'c ω').continuousOn, ?_, ?_⟩
  · intro t ht
    -- first for `Gtb`
    have hmain : IsStochConv P' V (ContinuousLinearMap.id ℝ H) Gtb 0 t (Z' t) := by
      intro ε hε
      obtain ⟨δ, hδ, hh⟩ := hZt t ht ε hε
      refine ⟨δ, hδ, fun n r h0 hl hmono hmesh => ?_⟩
      have hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) T := fun i => by
        have := Q48d.mem_Icc_of_part h0 hl hmono i
        exact ⟨this.1, this.2.trans ht.2⟩
      set Θ : PathSp T H → ℝ≥0∞ := fun y =>
        ‖pcm (h y) (Set.projIcc 0 T hT t) - rsFun V hT t r y‖ₑ ^ 2 with hΘ
      have hΘm : Measurable Θ := by
        refine Measurable.pow_const ?_ 2
        refine Measurable.enorm ?_
        refine Measurable.sub ?_ (continuous_rsFun V hT t r).measurable
        exact (continuous_eval_const (Set.projIcc 0 T hT t) : Continuous fun y : C(Set.Icc (0 : ℝ) T, H) =>
          y (Set.projIcc 0 T hT t)).measurable.comp hhm
      have e1 : ∫⁻ ω', ‖Z' t ω' - riemannSum V (ContinuousLinearMap.id ℝ H) Gtb t r ω'‖ₑ ^ 2 ∂P' =
          ∫⁻ ω', Θ (windowPath 0 T Gtb ω') ∂P' := by
        refine lintegral_congr fun ω' => ?_
        simp only [hΘ, hZ']
        rw [rsFun_windowPath V hT t r hr hctb ω']
      have e2 : ∫⁻ ω', Θ (windowPath 0 T Gtb ω') ∂P' = ∫⁻ ω, Θ (windowPath 0 T Gt ω) ∂P := by
        rw [← lintegral_map hΘm hpmb, ← lintegral_map hΘm hpm]
        have := hpathlaw
        unfold law at this
        rw [this]
      have e3 : ∫⁻ ω, Θ (windowPath 0 T Gt ω) ∂P =
          ∫⁻ ω, ‖Zb t ω - riemannSum V (ContinuousLinearMap.id ℝ H) Gt t r ω‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hZbh] with ω hω
        simp only [hΘ]
        rw [rsFun_windowPath V hT t r hr hct ω, hω t ht]
      rw [e1, e2, e3]
      exact hh n r h0 hl hmono hmesh
    exact isStochConv_congr_times P' V (ContinuousLinearMap.id ℝ H) ht.1
      (fun τ hτ => (hGGb τ ⟨hτ.1, hτ.2.trans ht.2⟩).symm) hmain
  · have hξm : Measurable ξ := hξ.mono (ℱ.le 0) le_rfl
    have hξ'm : Measurable ξ' := hξ'.mono (ℱ'.le 0) le_rfl
    have hΦ : Continuous (fun p : H × PathSp T H => vpathW V hc p.1 + p.2) :=
      ((continuous_vpathW V hT hc hB).comp continuous_fst).add continuous_snd
    have hmapf : Measurable (fun p : H × PathSp T H => (p.1, h p.2)) :=
      measurable_fst.prodMk (hhm.comp measurable_snd)
    set Ψ : H × PathSp T H → PathSp T H := fun p => vpathW V hc p.1 + h p.2 with hΨ
    have hΨm : Measurable Ψ := hΦ.measurable.comp hmapf
    have hjoint := joint_law_eq (P₁ := P) (P₂ := P') hT hGt hGtb hct hzt hctb hztb
      (ξ₁ := ξ) (ξ₂ := ξ') (hξ.mono (gfb4_aug_le P ℱ 0) le_rfl) (hξ'.mono (gfb4_aug_le P' ℱ' 0) le_rfl) hlaw
    have hpair : Measurable (fun ω => (ξ ω, windowPath 0 T Gt ω)) := hξm.prodMk hpm
    have hpairb : Measurable (fun ω' => (ξ' ω', windowPath 0 T Gtb ω')) := hξ'm.prodMk hpmb
    have hL : law P (windowPath 0 T (fun t ω => V t 0 (ξ ω) + Zb t ω)) =
        (P.map (fun ω => (ξ ω, windowPath 0 T Gt ω))).map Ψ := by
      rw [Measure.map_map hΨm hpair]
      unfold law
      refine Measure.map_congr ?_
      filter_upwards [hhae, hZc] with ω h1 h2
      rw [windowPath_vadd V hc ξ Zb h2, h1]
      rfl
    have hR : law P' (windowPath 0 T (fun t ω' => V t 0 (ξ' ω') + Z' t ω')) =
        (P'.map (fun ω' => (ξ' ω', windowPath 0 T Gtb ω'))).map Ψ := by
      rw [Measure.map_map hΨm hpairb]
      unfold law
      refine Measure.map_congr (Filter.Eventually.of_forall fun ω' => ?_)
      rw [windowPath_vadd V hc ξ' Z' (hZ'c ω').continuousOn]
      have : windowPath 0 T Z' ω' = h (windowPath 0 T Gtb ω') := by
        refine pcm_ext fun t => ?_
        rw [pcm_windowPath Z' (hZ'c ω').continuousOn]
        simp only [hZ', Set.projIcc_of_mem hT t.2]
      simp only [Function.comp, hΨ, this]
    rw [hL, hR, hjoint]

end Transfer

end HRS.Uniform.Comp28
