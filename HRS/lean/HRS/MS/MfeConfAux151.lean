import HRS.MS.MfeConfAux140

/-!
# S.B.1 (SB5), packet R3c (part 1): conditioning on an increasing family of events

Generic measure theory used to remove the initial conditioning: for events `A_j ↑` covering `Ω` a.e. and the conditioned measures
`cond Pm (A j)`, integrals against the laws of a map `Y` are `p_j⁻¹ ∫_{A_j} f(Y) dPm`; these converge to `∫ f(Y) dPm`
(`sb1_cond_tendsto`), nonnegative functions with uniformly bounded conditioned means are integrable (`sb1_cond_L1`), and the
relative entropy of a conditioned (restricted, renormalised) law is explicit (`sb1_klDiv_cond`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

section Cond

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {Pm : Measure Ω} [IsProbabilityMeasure Pm]

theorem sb1_cond_integral {A : Set Ω} {Y : Ω → α} (hY : Measurable Y) {f : α → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂((ProbabilityTheory.cond Pm A).map Y) = (Pm A).toReal⁻¹ * ∫ ζ in A, f (Y ζ) ∂Pm := by
  rw [integral_map hY.aemeasurable hf.aestronglyMeasurable, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  rfl

theorem sb1_cond_integrable {A : Set Ω} (hA : MeasurableSet A) (hp : Pm A ≠ 0) {Y : Ω → α} (hY : Measurable Y)
    {f : α → ℝ} (hf : Measurable f) :
    Integrable f ((ProbabilityTheory.cond Pm A).map Y) ↔ IntegrableOn (fun ζ => f (Y ζ)) A Pm := by
  rw [integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable, ProbabilityTheory.cond]
  have hne : (Pm A)⁻¹ ≠ 0 := by simp
  have htop : (Pm A)⁻¹ ≠ ⊤ := by simpa using hp
  rw [integrable_smul_measure hne htop]
  rfl

theorem sb1_cond_prob {A : Set Ω} (hA : MeasurableSet A) (hp : Pm A ≠ 0) : IsProbabilityMeasure (ProbabilityTheory.cond Pm A) :=
  cond_isProbabilityMeasure hp

variable {A : ℕ → Set Ω}

theorem sb1_cover_union (hcov : ∀ᵐ ζ ∂Pm, ∃ j, ζ ∈ A j) : Pm (⋃ j, A j) = 1 := by
  have : (⋃ j, A j) =ᵐ[Pm] (Set.univ : Set Ω) := by
    filter_upwards [hcov] with ζ hζ
    simp only [Set.mem_iUnion, Set.mem_univ, eq_iff_iff, iff_true]
    exact hζ
  rw [measure_congr this]; simp

theorem sb1_pj_tendsto (hA : ∀ j, MeasurableSet (A j)) (hmono : Monotone A) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, ζ ∈ A j) :
    Tendsto (fun j => (Pm (A j)).toReal) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := Pm) hmono
  rw [sb1_cover_union hcov] at h
  have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp h
  rw [ENNReal.toReal_one] at this
  exact this

theorem sb1_cond_tendsto (hA : ∀ j, MeasurableSet (A j)) (hmono : Monotone A) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, ζ ∈ A j)
    {g : Ω → ℝ} (hg : Integrable g Pm) :
    Tendsto (fun j => (Pm (A j)).toReal⁻¹ * ∫ ζ in A j, g ζ ∂Pm) atTop (𝓝 (∫ ζ, g ζ ∂Pm)) := by
  have h1 := tendsto_setIntegral_of_monotone (μ := Pm) (f := g) hA hmono hg.integrableOn
  have hU : (⋃ j, A j) =ᵐ[Pm] (Set.univ : Set Ω) := by
    filter_upwards [hcov] with ζ hζ
    simp only [Set.mem_iUnion, Set.mem_univ, eq_iff_iff, iff_true]
    exact hζ
  rw [setIntegral_congr_set hU, Measure.restrict_univ] at h1
  have h2 := (sb1_pj_tendsto hA hmono hcov).inv₀ one_ne_zero
  simpa using h2.mul h1

theorem sb1_cond_L1 (hA : ∀ j, MeasurableSet (A j)) (hmono : Monotone A) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, ζ ∈ A j)
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ζ, 0 ≤ F ζ) {B : ℝ} (hi : ∀ j, IntegrableOn F (A j) Pm)
    (hb : ∀ j, ∫ ζ in A j, F ζ ∂Pm ≤ B) : Integrable F Pm ∧ ∫ ζ, F ζ ∂Pm ≤ B := by
  set f : ℕ → Ω → ℝ≥0∞ := fun j => (A j).indicator (fun ζ => ENNReal.ofReal (F ζ)) with hf
  have hfm : ∀ j, Measurable (f j) := fun j => (ENNReal.measurable_ofReal.comp hF).indicator (hA j)
  have hfmono : Monotone f := fun i j hij ζ => by
    simp only [hf]
    exact Set.indicator_le_indicator_of_subset (hmono hij) (fun _ => bot_le) ζ
  have hsup : ∀ᵐ ζ ∂Pm, ⨆ j, f j ζ = ENNReal.ofReal (F ζ) := by
    filter_upwards [hcov] with ζ ⟨j, hj⟩
    refine le_antisymm (iSup_le fun i => Set.indicator_le_self' (fun _ _ => bot_le) ζ) ?_
    refine le_iSup_of_le j ?_
    simp [hf, hj]
  have hint : ∀ j, ∫⁻ ζ, f j ζ ∂Pm ≤ ENNReal.ofReal B := fun j => by
    simp only [hf]
    rw [lintegral_indicator (hA j), ← ofReal_integral_eq_lintegral_ofReal (hi j)
      (Filter.Eventually.of_forall fun ζ => hF0 ζ)]
    exact ENNReal.ofReal_le_ofReal (hb j)
  have htot : ∫⁻ ζ, ENNReal.ofReal (F ζ) ∂Pm ≤ ENNReal.ofReal B := by
    calc ∫⁻ ζ, ENNReal.ofReal (F ζ) ∂Pm = ∫⁻ ζ, ⨆ j, f j ζ ∂Pm := lintegral_congr_ae (hsup.mono fun ζ h => h.symm)
      _ = ⨆ j, ∫⁻ ζ, f j ζ ∂Pm := lintegral_iSup hfm hfmono
      _ ≤ _ := iSup_le hint
  have hfin : Integrable F Pm :=
    ⟨hF.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hF0)]
      exact lt_of_le_of_lt htot ENNReal.ofReal_lt_top⟩
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hF.aestronglyMeasurable]
  have hB : 0 ≤ B := by
    have := hb 0
    exact le_trans (setIntegral_nonneg (hA 0) fun ζ _ => hF0 ζ) this
  exact ENNReal.toReal_le_of_le_ofReal hB htot

end Cond

section Kl

variable {α : Type*} [MeasurableSpace α]

theorem sb1_klDiv_cond (ν Q : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure Q] (h : klDiv ν Q ≠ ⊤)
    {E : Set α} (hE : MeasurableSet E) (hp : ν E ≠ 0) :
    klDiv ((ν E)⁻¹ • ν.restrict E) Q ≠ ⊤ ∧
      (klDiv ((ν E)⁻¹ • ν.restrict E) Q).toReal =
        (ν E).toReal⁻¹ * ∫ x in E, llr ν Q x ∂ν - Real.log (ν E).toReal := by
  obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 h
  set c : ℝ≥0∞ := (ν E)⁻¹ with hc
  have hne : ν E ≠ ⊤ := measure_ne_top _ _
  have hc0 : c ≠ 0 := by simp [hc]
  have hctop : c ≠ ⊤ := by simpa [hc] using hp
  set μ' : Measure α := ν.restrict E with hμ'
  have hμ'ν : μ' ≪ ν := Measure.restrict_le_self.absolutelyContinuous
  have hμ'Q : μ' ≪ Q := hμ'ν.trans hνQ
  have hrn : μ'.rnDeriv Q =ᵐ[Q] E.indicator (ν.rnDeriv Q) := Measure.rnDeriv_restrict ν Q hE
  have hllr : llr μ' Q =ᵐ[μ'] llr ν Q := by
    have h1 : μ'.rnDeriv Q =ᵐ[μ'] E.indicator (ν.rnDeriv Q) := hμ'Q.ae_le hrn
    have h2 : ∀ᵐ x ∂μ', x ∈ E := ae_restrict_mem hE
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [llr_def]
    rw [hx1, Set.indicator_of_mem hx2]
  have hllr2 : llr (c • μ') Q =ᵐ[μ'] fun x => llr ν Q x + Real.log c.toReal := by
    filter_upwards [llr_smul_left hμ'Q c hc0 hctop, hllr] with x hx1 hx2
    rw [hx1, hx2]
  have hint' : Integrable (llr ν Q) μ' := hint.restrict
  have hI : Integrable (llr (c • μ') Q) (c • μ') := by
    rw [integrable_smul_measure hc0 hctop, integrable_congr hllr2]
    exact hint'.add (integrable_const _)
  have hac : c • μ' ≪ Q := hμ'Q.smul_left c
  refine ⟨klDiv_ne_top hac hI, ?_⟩
  have hmu : (c • μ') Set.univ = 1 := by
    simp only [hμ', Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul, hc]
    exact ENNReal.inv_mul_cancel hp hne
  haveI : IsProbabilityMeasure (c • μ') := ⟨hmu⟩
  rw [toReal_klDiv hac hI]
  simp only [probReal_univ]
  rw [integral_smul_measure, integral_congr_ae hllr2, integral_add hint' (integrable_const _), integral_const]
  have hcr : c.toReal = (ν E).toReal⁻¹ := by rw [hc, ENNReal.toReal_inv]
  have hpos : 0 < (ν E).toReal := ENNReal.toReal_pos hp hne
  have hμr : μ'.real Set.univ = (ν E).toReal := by
    simp [hμ', Measure.real, Measure.restrict_apply MeasurableSet.univ]
  rw [hμr, hcr, Real.log_inv]
  simp only [smul_eq_mul, hμ']
  field_simp
  ring

end Kl

section Init

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {Pm : Measure Ω} [IsProbabilityMeasure Pm]

theorem sb1_cond_map_event {X₀ : Ω → α} (hX₀ : Measurable X₀) {E : Set α} (hE : MeasurableSet E) :
    (ProbabilityTheory.cond Pm (X₀ ⁻¹' E)).map X₀ = (Pm.map X₀ E)⁻¹ • (Pm.map X₀).restrict E := by
  rw [ProbabilityTheory.cond, Measure.map_smul, Measure.map_apply hX₀ hE]
  congr 1
  · exact (Measure.restrict_map hX₀ hE).symm
  · exact hX₀.aemeasurable

/-- the initial entropies of the conditioned laws are finite and converge -/
theorem sb1_init_cond {X₀ : Ω → α} (hX₀ : Measurable X₀) {E : ℕ → Set α} (hE : ∀ j, MeasurableSet (E j))
    (hmono : Monotone E) (hpos : ∀ j, Pm (X₀ ⁻¹' E j) ≠ 0) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, X₀ ζ ∈ E j)
    (Q : Measure α) [IsProbabilityMeasure Q] (hfin : klDiv (Pm.map X₀) Q ≠ ⊤) :
    (∀ j, klDiv ((ProbabilityTheory.cond Pm (X₀ ⁻¹' E j)).map X₀) Q ≠ ⊤) ∧
      Tendsto (fun j => (klDiv ((ProbabilityTheory.cond Pm (X₀ ⁻¹' E j)).map X₀) Q).toReal) atTop
        (𝓝 (klDiv (Pm.map X₀) Q).toReal) := by
  haveI : IsProbabilityMeasure (Pm.map X₀) := (Measure.isProbabilityMeasure_map_iff hX₀.aemeasurable).2 inferInstance
  set ν := Pm.map X₀ with hν
  have hνE : ∀ j, ν (E j) = Pm (X₀ ⁻¹' E j) := fun j => Measure.map_apply hX₀ (hE j)
  have hp : ∀ j, ν (E j) ≠ 0 := fun j => by rw [hνE]; exact hpos j
  have hk := fun j => sb1_klDiv_cond ν Q hfin (hE j) (hp j)
  refine ⟨fun j => ?_, ?_⟩
  · rw [sb1_cond_map_event hX₀ (hE j)]; exact (hk j).1
  · obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 hfin
    have hcovν : ∀ᵐ x ∂ν, ∃ j, x ∈ E j := by
      have hm : MeasurableSet {x | ∃ j, x ∈ E j} := by
        have : {x | ∃ j, x ∈ E j} = ⋃ j, E j := by ext; simp
        rw [this]; exact MeasurableSet.iUnion hE
      rw [hν, ae_map_iff hX₀.aemeasurable hm]
      exact hcov
    have h1 := sb1_cond_tendsto (Pm := ν) hE hmono hcovν hint
    have h2 : Tendsto (fun j => Real.log (ν (E j)).toReal) atTop (𝓝 0) := by
      have := (sb1_pj_tendsto (Pm := ν) hE hmono hcovν)
      have h3 := (Real.continuousAt_log (one_ne_zero)).tendsto.comp this
      rw [Real.log_one] at h3
      exact h3
    have h4 := h1.sub h2
    have hlim : (klDiv ν Q).toReal = ∫ ζ, llr ν Q ζ ∂ν := by
      rw [toReal_klDiv hνQ hint]; simp
    rw [hlim]
    simp only [sub_zero] at h4
    refine h4.congr fun j => ?_
    rw [sb1_cond_map_event hX₀ (hE j), (hk j).2]

end Init

end HRS.MS.MfeConf
