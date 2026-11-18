import HRS.Stochastic.DDS
import HRS.Stochastic.TimeChange
import HRS.Stochastic.Wiener

/-!
# The Dambis–Dubins–Schwarz theorem: assembly (SI-01o)

Assembly of `dambis_dubins_schwarz` (statement formerly in `DDS.lean`) and of the proof of
`dds_coupling` (`dds_coupling_proof`) from the Brownian existence theorem (`Wiener.lean`) and the
time-change lemmas (`TimeChange.lean`).

Route.  (1) Clean versions `M₁, A₁` of `M, A` for the completed filtration `ℱ ⊔ nullSets P`
(`exists_clean`).  (2) Code `Ω` into the path space `CodedPath t` (a subtype of `ℝ → ℝ × ℝ`, so that
`Ω' : Type`), push `P` forward, and enlarge by an independent Brownian motion
(`exists_enlargement_indep`); the martingale properties of the coded path for the working filtration
`ddsFiltration` are transferred in `martingale_coded`.  (3) Extend beyond `t` by the Brownian motion
(`ExtData.tcData`), time-change (`timeChange_levy_hypotheses`), pass to a continuous modification and
conclude with `levy_characterization` (`ExtData.brownian_core`).  (4) Laws by `Measure.map_map`
(`law_coded`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Generic helpers -/

section Helpers

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Glue two martingale pieces at a time `c ≥ 0`: a process vanishing on `(-∞, 0]` that satisfies
the martingale identity on `[0, c]` and on `[c, ∞)` is a martingale. -/
theorem martingale_of_pieces {𝒢 : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ} {c : ℝ}
    (hZ : StronglyAdapted 𝒢 Z) (hzero : ∀ t ≤ 0, ∀ ω, Z t ω = 0)
    (h₁ : ∀ s r, 0 ≤ s → s ≤ r → r ≤ c → P[Z r | 𝒢 s] =ᵐ[P] Z s)
    (h₂ : ∀ s r, c ≤ s → s ≤ r → P[Z r | 𝒢 s] =ᵐ[P] Z s) : Martingale Z 𝒢 P := by
  refine martingale_of_nonneg_times hZ hzero fun s r hs hsr => ?_
  by_cases hrc : r ≤ c
  · exact h₁ s r hs hsr hrc
  by_cases hcs : c ≤ s
  · exact h₂ s r hcs hsr
  push Not at hrc hcs
  calc P[Z r | 𝒢 s] =ᵐ[P] P[P[Z r | 𝒢 c] | 𝒢 s] :=
        (condExp_condExp_of_le (𝒢.mono hcs.le) (𝒢.le c)).symm
    _ =ᵐ[P] P[Z c | 𝒢 s] := condExp_congr_ae (h₂ c r le_rfl hrc.le)
    _ =ᵐ[P] Z s := h₁ s c hs hcs.le le_rfl

omit [IsProbabilityMeasure P] in
/-- A sub-filtration to which the Brownian motion is still adapted keeps the Brownian property. -/
theorem IsBrownianFiltration.of_le_of_adapted {ι : Type*} [Fintype ι] {ℱ 𝒢 : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) (hle : ∀ u, 𝒢 u ≤ ℱ u)
    (hc : IsCompleteFiltration P 𝒢) (had : ∀ u : ℝ≥0, Measurable[𝒢 u] (W u)) :
    IsBrownianFiltration P 𝒢 W :=
  ⟨hc, had, hW.zero, hW.cont, fun s t hst => indep_of_indep_of_le_right (hW.indep_incr s t hst) (hle s),
    hW.gaussian_incr⟩


/-- Conditional expectation given `𝒜 ⊔ ℬ` of an `𝒜'`-measurable function, with `ℬ` independent of
`𝒜'` and `𝒜 ≤ 𝒜'`. -/
theorem condExp_sup_of_indep {𝒜 𝒜' ℬ : MeasurableSpace Ω} (h𝒜' : 𝒜' ≤ mΩ) (hℬ : ℬ ≤ mΩ)
    (h𝒜 : 𝒜 ≤ 𝒜') (hind : Indep 𝒜' ℬ P) {f : Ω → ℝ} (hfi : Integrable f P)
    (hf : StronglyMeasurable[𝒜'] f) : P[f | 𝒜 ⊔ ℬ] =ᵐ[P] P[f | 𝒜] := by
  letI : MeasurableSpace Ω := mΩ
  have h𝒜m : 𝒜 ≤ mΩ := h𝒜.trans h𝒜'
  have hle : 𝒜 ⊔ ℬ ≤ mΩ := sup_le h𝒜m hℬ
  -- rectangle integrals of `𝒜'`-measurable functions factor
  have key : ∀ {F : Ω → ℝ}, StronglyMeasurable[𝒜'] F → ∀ {a b : Set Ω},
      MeasurableSet[𝒜] a → MeasurableSet[ℬ] b →
      ∫ ω in a ∩ b, F ω ∂P = (∫ ω in a, F ω ∂P) * P.real b := by
    intro F hF a b ha hb
    have ha' : MeasurableSet[𝒜'] a := h𝒜 _ ha
    have hX : StronglyMeasurable[𝒜'] (a.indicator F) := hF.indicator ha'
    have hY : Measurable[ℬ] (b.indicator fun _ : Ω => (1 : ℝ)) :=
      measurable_const.indicator hb
    have hXY : IndepFun (a.indicator F) (b.indicator fun _ : Ω => (1 : ℝ)) P :=
      (IndepFun_iff_Indep _ _ _).2
        (indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hX.measurable.comap_le)
          hY.comap_le)
    have h1 : ∫ ω in a ∩ b, F ω ∂P = ∫ ω, a.indicator F ω * b.indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [← integral_indicator ((h𝒜m _ ha).inter (hℬ _ hb))]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h1 : ω ∈ a <;> by_cases h2 : ω ∈ b <;> simp [h1, h2]
    rw [h1, hXY.integral_fun_mul_eq_mul_integral (hX.mono h𝒜').aestronglyMeasurable
      (hY.mono hℬ le_rfl).aestronglyMeasurable, integral_indicator (h𝒜m _ ha)]
    congr 1
    rw [integral_indicator (hℬ _ hb)]
    simp [measureReal_def]
  have hgsm : StronglyMeasurable[𝒜'] (P[f | 𝒜]) := stronglyMeasurable_condExp.mono h𝒜
  have hgi : Integrable (P[f | 𝒜]) P := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hfi (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => ?_) (stronglyMeasurable_condExp.mono (le_sup_left : 𝒜 ≤ 𝒜 ⊔ ℬ)).aestronglyMeasurable).symm
  -- the π-system of rectangles generates `𝒜 ⊔ ℬ`
  let p : Set (Set Ω) := {s | ∃ a b, MeasurableSet[𝒜] a ∧ MeasurableSet[ℬ] b ∧ s = a ∩ b}
  have hπ : IsPiSystem p := by
    rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
    exact ⟨a ∩ a', b ∩ b', @MeasurableSet.inter Ω 𝒜 _ _ ha ha',
      @MeasurableSet.inter Ω ℬ _ _ hb hb', by ext; simp; tauto⟩
  have hgen : 𝒜 ⊔ ℬ = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le (fun a ha => MeasurableSpace.measurableSet_generateFrom ⟨a, Set.univ, ha,
        @MeasurableSet.univ Ω ℬ, by simp⟩) (fun b hb => MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, b, @MeasurableSet.univ Ω 𝒜, hb, by simp⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact @MeasurableSet.inter Ω (𝒜 ⊔ ℬ) _ _ (le_sup_left (a := 𝒜) (b := ℬ) _ ha)
        (le_sup_right (a := 𝒜) (b := ℬ) _ hb)
  refine MeasurableSpace.induction_on_inter (m := 𝒜 ⊔ ℬ)
    (C := fun s _ => ∫ x in s, (P[f | 𝒜]) x ∂P = ∫ x in s, f x ∂P) hgen hπ ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    rw [key hgsm ha hb, key hf ha hb, setIntegral_condExp h𝒜m hfi ha]
  · intro s hs h
    have hs' : MeasurableSet s := hle _ hs
    have e1 := integral_add_compl hs' hgi
    have e2 := integral_add_compl hs' hfi
    rw [integral_condExp h𝒜m] at e1
    linarith
  · intro g hdisj hg h
    have hg' : ∀ i, MeasurableSet (g i) := fun i => hle _ (hg i)
    rw [integral_iUnion (f := P[f | 𝒜]) (μ := P) hg' hdisj hgi.integrableOn,
      integral_iUnion (f := f) (μ := P) hg' hdisj hfi.integrableOn]
    exact tsum_congr h

end Helpers

/-! ### B.1.1 Clean versions -/

section Clean

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- `ℱ u ⊔ nullSets P`, the completed filtration. -/
def augFiltration (P : Measure Ω) (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq u := ℱ u ⊔ nullSets P
  mono' := fun _ _ h => sup_le_sup_right (ℱ.mono h) _
  le' := fun u => sup_le (ℱ.le u) (nullSets_le P)

theorem augFiltration_isComplete (ℱ : Filtration ℝ mΩ) :
    IsCompleteFiltration P (augFiltration P ℱ) := by
  intro t s hs hP
  have h1 : MeasurableSet[nullSets P] s := MeasurableSpace.measurableSet_generateFrom ⟨hs, hP⟩
  exact (le_sup_right : nullSets P ≤ _) s h1

theorem martingale_aug {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P) :
    Martingale M (augFiltration P ℱ) P :=
  ⟨fun s => (hM.1 s).mono (le_sup_left : ℱ s ≤ ℱ s ⊔ nullSets P),
    fun i j hij => (condExp_sup_nullSets (ℱ.le i) (M j)).trans (hM.2 i j hij)⟩

/-- Everywhere-clean data for the DDS construction: a complete filtration, a martingale `M` and an
adapted `A` with `M² - A` a martingale, all path properties holding for every `ω`. -/
structure CleanData (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (t : ℝ) (M A : ℝ → Ω → ℝ) : Prop where
  complete : IsCompleteFiltration P ℱ
  mart : Martingale M ℱ P
  qmart : Martingale (fun s ω => M s ω ^ 2 - A s ω) ℱ P
  adaptedA : Adapted ℱ A
  zeroM : ∀ ω, M 0 ω = 0
  zeroA : ∀ ω, A 0 ω = 0
  contM : ∀ ω, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t)
  contA : ∀ ω, ContinuousOn (fun τ => A τ ω) (Set.Icc 0 t)
  monoA : ∀ ω, MonotoneOn (fun τ => A τ ω) (Set.Icc 0 t)
  memLp : ∀ τ ∈ Set.Icc 0 t, MemLp (M τ) 2 P
  intA : Integrable (A t) P

theorem exists_clean {ℱ : Filtration ℝ mΩ} {t : ℝ} {M A : ℝ → Ω → ℝ}
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) :
    ∃ M₁ A₁ : ℝ → Ω → ℝ, CleanData P (augFiltration P ℱ) t M₁ A₁ ∧
      (∀ s, M₁ s =ᵐ[P] M s) ∧ ∀ s, A₁ s =ᵐ[P] A s := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ : ∃ N : Set Ω, {ω | ¬ (M 0 ω = 0 ∧ A 0 ω = 0 ∧
      ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t) ∧ ContinuousOn (fun τ => A τ ω) (Set.Icc 0 t) ∧
      MonotoneOn (fun τ => A τ ω) (Set.Icc 0 t))} ⊆ N ∧ MeasurableSet N ∧ P N = 0 := by
    have h0 := ae_iff.1 (hM.zero.and (hA.zero.and (hM.cont.and (hA.cont.and hA.mono))))
    exact ⟨toMeasurable P _, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
      by rw [measure_toMeasurable]; exact h0⟩
  have hgood : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ A 0 ω = 0 ∧
      ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t) ∧ ContinuousOn (fun τ => A τ ω) (Set.Icc 0 t) ∧
      MonotoneOn (fun τ => A τ ω) (Set.Icc 0 t) := by
    intro ω hω
    by_contra h
    exact hω (hNsub h)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hN0
  refine ⟨fun s ω => if ω ∈ N then 0 else M s ω, fun s ω => if ω ∈ N then 0 else A s ω, ?_, ?_, ?_⟩
  swap
  · intro s; filter_upwards [hNae] with ω hω; simp [hω]
  swap
  · intro s; filter_upwards [hNae] with ω hω; simp [hω]
  have hN' : ∀ s, MeasurableSet[augFiltration P ℱ s] N := fun s =>
    augFiltration_isComplete ℱ s N hNm hN0
  have hae1 : ∀ s, (fun ω => if ω ∈ N then (0 : ℝ) else M s ω) =ᵐ[P] M s := by
    intro s; filter_upwards [hNae] with ω hω; simp [hω]
  have hae2 : ∀ s, (fun ω => if ω ∈ N then (0 : ℝ) else A s ω) =ᵐ[P] A s := by
    intro s; filter_upwards [hNae] with ω hω; simp [hω]
  have hadM : ∀ s, Measurable[augFiltration P ℱ s] (fun ω => if ω ∈ N then (0 : ℝ) else M s ω) :=
    fun s => Measurable.ite (hN' s) measurable_const
      ((hM.martingale.1 s).measurable.mono (le_sup_left : ℱ s ≤ ℱ s ⊔ nullSets P) le_rfl)
  have hadA : ∀ s, Measurable[augFiltration P ℱ s] (fun ω => if ω ∈ N then (0 : ℝ) else A s ω) :=
    fun s => Measurable.ite (hN' s) measurable_const
      ((hA.adapted s).mono (le_sup_left : ℱ s ≤ ℱ s ⊔ nullSets P) le_rfl)
  refine ⟨augFiltration_isComplete ℱ, ?_, ?_, hadA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact martingale_congr_ae (martingale_aug hM.martingale) (fun s => (hadM s).stronglyMeasurable) hae1
  · refine martingale_congr_ae (martingale_aug hA.compensator) (fun s => ?_) (fun s => ?_)
    · exact (((hadM s).pow_const 2).sub (hadA s)).stronglyMeasurable
    · filter_upwards [hae1 s, hae2 s] with ω h1 h2
      simp only [h1, h2]
  · intro ω; by_cases hω : ω ∈ N
    · simp [hω]
    · simp [hω, (hgood ω hω).1]
  · intro ω; by_cases hω : ω ∈ N
    · simp [hω]
    · simp [hω, (hgood ω hω).2.1]
  · intro ω; by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuousOn_const
    · simp only [hω, ite_false]; exact (hgood ω hω).2.2.1
  · intro ω; by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuousOn_const
    · simp only [hω, ite_false]; exact (hgood ω hω).2.2.2.1
  · intro ω; by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact monotoneOn_const
    · simp only [hω, ite_false]; exact (hgood ω hω).2.2.2.2
  · intro τ hτ
    exact (memLp_congr_ae (hae1 τ)).2 (hM.sq_int τ hτ)
  · exact hint.congr (hae2 t).symm

end Clean

/-! ### B.1.2 Path space and coding -/

/-- Coded paths on `[0, t]`: all of `ℝ → ℝ × ℝ`, continuous with monotone second component on
`[0, t]` and vanishing at `0`. -/
abbrev CodedPath (t : ℝ) : Type :=
  {x : ℝ → ℝ × ℝ // ContinuousOn x (Set.Icc 0 t) ∧
    MonotoneOn (fun τ => (x τ).2) (Set.Icc 0 t) ∧ x 0 = 0}

theorem measurable_pathEval {t : ℝ} (τ : ℝ) : Measurable fun x : CodedPath t => x.1 τ :=
  (measurable_pi_apply τ).comp measurable_subtype_coe

set_option warn.classDefReducibility false in
/-- The σ-algebra of the coded path up to time `u`. -/
def pathSigma (t u : ℝ) : MeasurableSpace (CodedPath t) :=
  ⨆ (r : ℝ) (_ : r ≤ u), MeasurableSpace.comap (fun x : CodedPath t => x.1 r) inferInstance

theorem pathSigma_le (t u : ℝ) : pathSigma t u ≤ (inferInstance : MeasurableSpace (CodedPath t)) :=
  iSup₂_le fun r _ => (measurable_pathEval r).comap_le

theorem measurable_pathEval_sigma {t : ℝ} {τ u : ℝ} (h : τ ≤ u) :
    Measurable[pathSigma t u] fun x : CodedPath t => x.1 τ :=
  Measurable.of_comap_le (le_iSup₂_of_le τ h le_rfl)

section Coding

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {t : ℝ} {M A : ℝ → Ω → ℝ}

/-- The coding of `Ω` into the path space. -/
def codeMap (hc : CleanData P ℱ t M A) : Ω → CodedPath t := fun ω =>
  ⟨fun τ => (M τ ω, A τ ω), (hc.contM ω).prodMk (hc.contA ω),
    fun _ ha _ hb hab => hc.monoA ω ha hb hab, Prod.ext (hc.zeroM ω) (hc.zeroA ω)⟩

theorem codeMap_apply (hc : CleanData P ℱ t M A) (ω : Ω) (τ : ℝ) :
    (codeMap hc ω).1 τ = (M τ ω, A τ ω) := rfl

theorem measurable_codeMap_sigma (hc : CleanData P ℱ t M A) (s : ℝ) :
    Measurable[ℱ s, pathSigma t s] (codeMap hc) := by
  refine @Measurable.of_comap_le _ _ (ℱ s) (pathSigma t s) _ ?_
  unfold pathSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun r => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hr => ?_
  rw [MeasurableSpace.comap_comp]
  refine (@Measurable.comap_le _ _ (ℱ s) _ _ ?_)
  have h1 : Measurable[ℱ s] (M r) := ((hc.mart.1 r).measurable).mono (ℱ.mono hr) le_rfl
  have h2 : Measurable[ℱ s] (A r) := (hc.adaptedA r).mono (ℱ.mono hr) le_rfl
  exact h1.prodMk h2

theorem measurable_codeMap (hc : CleanData P ℱ t M A) : Measurable (codeMap hc) :=
  by
  unfold codeMap
  refine Measurable.subtype_mk ?_
  exact Measurable.of_eval fun τ =>
    (((hc.mart.1 τ).measurable.mono (ℱ.le τ) le_rfl).prodMk
      ((hc.adaptedA τ).mono (ℱ.le τ) le_rfl))

end Coding

/-! ### B.1.3 The enlarged space and its filtration -/

/-- `exists_enlargement` with the explicit independence of the enlarged datum from the Brownian
paths (the proof of `exists_enlargement`, keeping the independence statement). -/
theorem exists_enlargement_indep (ι : Type) [Fintype ι] (E : Type) [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    ∃ (W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ) (hW : ∀ t, Measurable (W t)),
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
      IndepFun Prod.fst (fun p t => W t p) (μ.prod (Measure.pi fun _ : ι => wienerMeasure)) ∧
      IsBrownianFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
        (generatedFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
          Prod.fst measurable_fst W hW) W := by
  set ν : Measure (ι → WienerSeq) := Measure.pi fun _ : ι => wienerMeasure with hν
  set W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ := fun t p k => wienerPath t (p.2 k) with hWdef
  have hW : ∀ t, Measurable (W t) := fun t =>
    Measurable.of_eval fun k => (measurable_wienerPath t).comp
      ((measurable_pi_apply k).comp measurable_snd)
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => funext fun k => wienerPath_zero _
  have hWc : ∀ ω, Continuous fun t => W t ω := fun ω =>
    continuous_pi fun k => continuous_wienerPath _
  have hX₀W : IndepFun Prod.fst (fun p : E × (ι → WienerSeq) => fun t => W t p) (μ.prod ν) :=
    indepFun_prod (μ := μ) (ν := ν) (X := id)
      (Y := fun (ω : ι → WienerSeq) (t : ℝ≥0) (k : ι) => wienerPath t (ω k)) measurable_id
      (Measurable.of_eval fun t => Measurable.of_eval fun k =>
        (measurable_wienerPath t).comp (measurable_pi_apply k))
  refine ⟨W, hW, hW0, hWc, hX₀W, ?_⟩
  have hsnd : MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2) (μ.prod ν) ν :=
    measurePreserving_snd
  have hev : ∀ k : ι, MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2 k) (μ.prod ν)
      wienerMeasure := fun k =>
    (measurePreserving_eval (fun _ : ι => wienerMeasure) k).comp hsnd
  have hB : ∀ k, IsBrownianReal (fun t p => W t p k) (μ.prod ν) := fun k =>
    IsBrownianReal.comp_measurePreserving (hev k) isPreBrownianReal_wienerPath
      continuous_wienerPath
  have hpath : Measurable fun (ω : WienerSeq) (t : ℝ≥0) => wienerPath t ω :=
    Measurable.of_eval measurable_wienerPath
  have hind0 : iIndepFun (fun (k : ι) (ω : ι → WienerSeq) => fun t : ℝ≥0 => wienerPath t (ω k)) ν :=
    iIndepFun_pi (μ := fun _ : ι => wienerMeasure) (X := fun _ => fun ω t => wienerPath t ω)
      (fun _ => hpath.aemeasurable)
  have hind : iIndepFun (fun (k : ι) (p : E × (ι → WienerSeq)) => fun t : ℝ≥0 => W t p k)
      (μ.prod ν) :=
    iIndepFun_comp_measurePreserving hsnd (X := fun (k : ι) (ω : ι → WienerSeq) =>
      fun t : ℝ≥0 => wienerPath t (ω k))
      (fun k => Measurable.of_eval fun t => (measurable_wienerPath t).comp (measurable_pi_apply k))
      hind0
  exact isBrownianFiltration_generated (μ.prod ν) W hW hB hind hW0 hWc Prod.fst measurable_fst
    hX₀W

/-- The enlarged space `CodedPath t × Wiener^1`. -/
abbrev DDSSpace (t : ℝ) : Type := CodedPath t × (Fin 1 → WienerSeq)

set_option warn.classDefReducibility false in
/-- The coded-path part of the working filtration. -/
def pathPart (t u : ℝ) : MeasurableSpace (DDSSpace t) := (pathSigma t u).comap Prod.fst

set_option warn.classDefReducibility false in
/-- The Brownian part of the working filtration. -/
def wienerPart (t : ℝ) (W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ) (u : ℝ) : MeasurableSpace (DDSSpace t) :=
  ⨆ (r : ℝ≥0) (_ : (r : ℝ) ≤ u), MeasurableSpace.comap (W r) inferInstance

theorem pathPart_le {t : ℝ} (u : ℝ) :
    pathPart t u ≤ (MeasurableSpace.comap Prod.fst inferInstance : MeasurableSpace (DDSSpace t)) :=
  MeasurableSpace.comap_mono (pathSigma_le t u)

/-- The working filtration `𝒢 u = (σ(coded path up to u) ⊔ σ(W_r, r ≤ u)) ⊔ nullSets`. -/
def ddsFiltration (t : ℝ) (P' : Measure (DDSSpace t)) (W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ)
    (hW : ∀ r, Measurable (W r)) : Filtration ℝ (inferInstance : MeasurableSpace (DDSSpace t)) where
  seq u := (pathPart t u ⊔ wienerPart t W u) ⊔ nullSets P'
  mono' := by
    intro u u' h
    refine sup_le_sup_right (sup_le_sup ?_ ?_) _
    · exact MeasurableSpace.comap_mono (iSup₂_mono' fun r hr => ⟨r, hr.trans h, le_rfl⟩)
    · exact iSup₂_mono' fun r hr => ⟨r, hr.trans h, le_rfl⟩
  le' u := sup_le (sup_le ((pathPart_le u).trans measurable_fst.comap_le)
    (iSup₂_le fun r _ => (hW r).comap_le)) (nullSets_le P')

theorem pathPart_le_ddsFiltration {t : ℝ} {P' : Measure (DDSSpace t)}
    {W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ} {hW : ∀ r, Measurable (W r)} (u : ℝ) :
    pathPart t u ≤ ddsFiltration t P' W hW u :=
  (le_sup_left : pathPart t u ≤ _ ⊔ wienerPart t W u).trans le_sup_left

theorem wienerPart_le_ddsFiltration {t : ℝ} {P' : Measure (DDSSpace t)}
    {W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ} {hW : ∀ r, Measurable (W r)} (u : ℝ) :
    wienerPart t W u ≤ ddsFiltration t P' W hW u :=
  (le_sup_right : wienerPart t W u ≤ pathPart t u ⊔ _).trans le_sup_left

theorem ddsFiltration_le_generated {t : ℝ} {P' : Measure (DDSSpace t)}
    {W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ} {hW : ∀ r, Measurable (W r)} (u : ℝ) :
    ddsFiltration t P' W hW u ≤ generatedFiltration P' Prod.fst measurable_fst W hW u := by
  refine sup_le_sup_right (sup_le ((pathPart_le u).trans le_sup_left) ?_) _
  exact le_sup_right

/-! ### B.1.7 Transfer of the martingale property along the coding -/

section Transfer

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {t : ℝ} {M A : ℝ → Ω → ℝ}

theorem wienerPart_le_comap_path {t : ℝ} (W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ) (u : ℝ) :
    wienerPart t W u ≤ MeasurableSpace.comap (fun p τ => W τ p) inferInstance := by
  refine iSup₂_le fun r _ => ?_
  have : (W r) = (fun f : ℝ≥0 → Fin 1 → ℝ => f r) ∘ (fun p τ => W τ p) := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply r).comap_le

theorem martingale_coded (hc : CleanData P ℱ t M A) (G : ℝ → ℝ × ℝ → ℝ)
    (hG : ∀ τ, Measurable (G τ))
    (hY : Martingale (fun τ ω => G τ (M τ ω, A τ ω)) ℱ P)
    {W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ} (hW : ∀ r, Measurable (W r))
    (hind : IndepFun Prod.fst (fun p τ => W τ p)
      ((P.map (codeMap hc)).prod (Measure.pi fun _ : Fin 1 => wienerMeasure))) :
    Martingale (fun τ (p : DDSSpace t) => G τ (p.1.1 τ))
      (ddsFiltration t ((P.map (codeMap hc)).prod (Measure.pi fun _ : Fin 1 => wienerMeasure)) W hW)
      ((P.map (codeMap hc)).prod (Measure.pi fun _ : Fin 1 => wienerMeasure)) := by
  set μ₁ := P.map (codeMap hc) with hμ₁
  set ν : Measure (Fin 1 → WienerSeq) := Measure.pi fun _ : Fin 1 => wienerMeasure with hν
  have : IsProbabilityMeasure μ₁ := by rw [hμ₁]; infer_instance
  set P' := μ₁.prod ν with hP'
  have hψ : ∀ τ, Measurable fun x : CodedPath t => G τ (x.1 τ) := fun τ =>
    (hG τ).comp (measurable_pathEval τ)
  have hψσ : ∀ τ, Measurable[pathSigma t τ] fun x : CodedPath t => G τ (x.1 τ) := fun τ =>
    (hG τ).comp (measurable_pathEval_sigma le_rfl)
  have hfst : MeasurePreserving (Prod.fst : DDSSpace t → CodedPath t) P' μ₁ := measurePreserving_fst
  have hint : ∀ τ, Integrable (fun p : DDSSpace t => G τ (p.1.1 τ)) P' := fun τ => by
    have h1 : Integrable (fun x : CodedPath t => G τ (x.1 τ)) μ₁ :=
      (integrable_map_measure (hψ τ).aestronglyMeasurable
        (measurable_codeMap hc).aemeasurable).2 (hY.integrable τ)
    exact hfst.integrable_comp_of_integrable h1
  have hfm : ∀ τ, StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
      (fun p : DDSSpace t => G τ (p.1.1 τ)) := fun τ =>
    ((hψ τ).comp (comap_measurable (Prod.fst : DDSSpace t → CodedPath t))).stronglyMeasurable
  have hgm : ∀ τ, StronglyMeasurable[pathPart t τ] (fun p : DDSSpace t => G τ (p.1.1 τ)) :=
    fun τ => ((hψσ τ).comp (comap_measurable (Prod.fst : DDSSpace t → CodedPath t))).stronglyMeasurable
  refine ⟨fun τ => (hgm τ).mono (pathPart_le_ddsFiltration τ), fun s r hsr => ?_⟩
  have hind' : Indep (MeasurableSpace.comap Prod.fst inferInstance : MeasurableSpace (DDSSpace t))
      (wienerPart t W s) P' :=
    indep_of_indep_of_le_right ((IndepFun_iff_Indep _ _ _).1 hind) (wienerPart_le_comap_path W s)
  have hle1 : pathPart t s ≤ (MeasurableSpace.comap Prod.fst inferInstance :
      MeasurableSpace (DDSSpace t)) := pathPart_le s
  have hle2 : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (DDSSpace t)) := measurable_fst.comap_le
  have hle3 : wienerPart t W s ≤ (inferInstance : MeasurableSpace (DDSSpace t)) :=
    (wienerPart_le_ddsFiltration (P' := P') (hW := hW) s).trans ((ddsFiltration t P' W hW).le s)
  have e1 : P'[fun p : DDSSpace t => G r (p.1.1 r) | ddsFiltration t P' W hW s] =ᵐ[P']
      P'[fun p : DDSSpace t => G r (p.1.1 r) | pathPart t s ⊔ wienerPart t W s] :=
    condExp_sup_nullSets (sup_le (hle1.trans hle2) hle3) _
  have e2 := condExp_sup_of_indep (P := P') (𝒜 := pathPart t s) hle2 hle3 hle1 hind' (hint r) (hfm r)
  have e3 : (fun p : DDSSpace t => G s (p.1.1 s)) =ᵐ[P']
      P'[fun p : DDSSpace t => G r (p.1.1 r) | pathPart t s] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (hle1.trans hle2) (hint r)
      (fun S _ _ => (hint s).integrableOn) (fun S hS _ => ?_)
      (hgm s).aestronglyMeasurable
    obtain ⟨H, hH, rfl⟩ := hS
    have hHfull : MeasurableSet H := pathSigma_le t s _ hH
    have e : P'.map Prod.fst = μ₁ := hfst.map_eq
    have key : ∀ τ, ∫ p in (Prod.fst : DDSSpace t → CodedPath t) ⁻¹' H, G τ (p.1.1 τ) ∂P' =
        ∫ ω in codeMap hc ⁻¹' H, G τ (M τ ω, A τ ω) ∂P := by
      intro τ
      have h1 := setIntegral_map (μ := P') (g := (Prod.fst : DDSSpace t → CodedPath t))
        (f := fun x : CodedPath t => G τ (x.1 τ)) hHfull
        (by rw [e]; exact (hψ τ).aestronglyMeasurable) measurable_fst.aemeasurable
      rw [e] at h1
      have h2 := setIntegral_map (μ := P) (g := codeMap hc)
        (f := fun x : CodedPath t => G τ (x.1 τ)) hHfull
        (hψ τ).aestronglyMeasurable (measurable_codeMap hc).aemeasurable
      exact h1.symm.trans h2
    rw [key s, key r]
    exact hY.setIntegral_eq hsr (measurable_codeMap_sigma hc s hH)
  exact e1.trans (e2.trans e3.symm)

end Transfer

/-! ### B.7.1 Extension beyond `t` by an independent Brownian motion -/

section Extension

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂}

/-- Clamp a time into `[0, t]`. -/
def clampT (t s : ℝ) : ℝ := max (min s t) 0

/-- The real-time scalar Brownian path. -/
def bw (W : ℝ≥0 → Ω₂ → Fin 1 → ℝ) (s : ℝ) (ω : Ω₂) : ℝ := ofNNRealTime W s ω 0

/-- The extension of `M'` beyond `t` by `W`. -/
def Mext (W : ℝ≥0 → Ω₂ → Fin 1 → ℝ) (M' : ℝ → Ω₂ → ℝ) (t s : ℝ) (ω : Ω₂) : ℝ :=
  M' (clampT t s) ω + (bw W s ω - bw W (min s t) ω)

/-- The extension of `A'` beyond `t` by a linear drift. -/
def Aext (A' : ℝ → Ω₂ → ℝ) (t s : ℝ) (ω : Ω₂) : ℝ := A' (clampT t s) ω + (max s t - t)

theorem clampT_mem {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : clampT t s ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) ht⟩

theorem clampT_of_mem {t s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) : clampT t s = s := by
  unfold clampT; rw [min_eq_left hs.2, max_eq_left hs.1]

theorem clampT_of_nonpos {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 0) : clampT t s = 0 := by
  unfold clampT; rw [min_eq_left (hs.trans ht), max_eq_right hs]

theorem clampT_of_ge {t s : ℝ} (ht : 0 ≤ t) (hs : t ≤ s) : clampT t s = t := by
  unfold clampT; rw [min_eq_right hs, max_eq_left ht]

theorem clampT_le {t s : ℝ} (hs : 0 ≤ s) : clampT t s ≤ s :=
  max_le (min_le_left _ _) hs

theorem continuous_clampT (t : ℝ) : Continuous (clampT t) := by
  unfold clampT; fun_prop

theorem monotone_clampT (t : ℝ) : Monotone (clampT t) := fun a b hab => by
  unfold clampT; exact max_le_max (min_le_min_right _ hab) le_rfl

end Extension

section Extension2

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝒢 : Filtration ℝ m₂} {W : ℝ≥0 → Ω₂ → Fin 1 → ℝ} {t : ℝ} {M' A' : ℝ → Ω₂ → ℝ}

/-- Hypotheses for the extension of `(M', A')` beyond `t`. -/
structure ExtData (P₂ : Measure Ω₂) (𝒢 : Filtration ℝ m₂) (W : ℝ≥0 → Ω₂ → Fin 1 → ℝ) (t : ℝ)
    (M' A' : ℝ → Ω₂ → ℝ) : Prop where
  bf : IsBrownianFiltration P₂ 𝒢 W
  ht : 0 ≤ t
  mart : Martingale M' 𝒢 P₂
  qmart : Martingale (fun τ ω => M' τ ω ^ 2 - A' τ ω) 𝒢 P₂
  memLp : ∀ τ ∈ Set.Icc 0 t, MemLp (M' τ) 2 P₂
  adaptedA : Adapted 𝒢 A'
  zeroM : ∀ ω, M' 0 ω = 0
  zeroA : ∀ ω, A' 0 ω = 0
  contM : ∀ ω, ContinuousOn (fun τ => M' τ ω) (Set.Icc 0 t)
  contA : ∀ ω, ContinuousOn (fun τ => A' τ ω) (Set.Icc 0 t)
  monoA : ∀ ω, MonotoneOn (fun τ => A' τ ω) (Set.Icc 0 t)

namespace ExtData

variable (h : ExtData P₂ 𝒢 W t M' A')
include h

theorem stronglyMeasurable_clampM (s : ℝ) : StronglyMeasurable[𝒢 s] (M' (clampT t s)) := by
  by_cases hs : 0 ≤ s
  · exact (h.mart.1 (clampT t s)).mono (𝒢.mono (clampT_le hs))
  · have : M' (clampT t s) = fun _ => 0 := by
      rw [clampT_of_nonpos h.ht (not_le.1 hs).le]; funext ω; exact h.zeroM ω
    rw [this]; exact stronglyMeasurable_const

theorem measurable_clampA (s : ℝ) : Measurable[𝒢 s] (A' (clampT t s)) := by
  by_cases hs : 0 ≤ s
  · exact (h.adaptedA (clampT t s)).mono (𝒢.mono (clampT_le hs)) le_rfl
  · have : A' (clampT t s) = fun _ => 0 := by
      rw [clampT_of_nonpos h.ht (not_le.1 hs).le]; funext ω; exact h.zeroA ω
    rw [this]; exact measurable_const

theorem stronglyMeasurable_bw (s : ℝ) : StronglyMeasurable[𝒢 s] (bw W s) :=
  h.bf.stronglyMeasurable_ofNNRealTime_coord s 0

theorem stronglyMeasurable_Mext (s : ℝ) : StronglyMeasurable[𝒢 s] (Mext W M' t s) :=
  (h.stronglyMeasurable_clampM s).add
    ((h.stronglyMeasurable_bw s).sub
      ((h.stronglyMeasurable_bw (min s t)).mono (𝒢.mono (min_le_left _ _))))

theorem adapted_Aext (s : ℝ) : Measurable[𝒢 s] (Aext A' t s) :=
  (h.measurable_clampA s).add_const _

theorem Mext_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) : Mext W M' t s = M' s := by
  funext ω
  simp only [Mext, clampT_of_mem hs, min_eq_left hs.2, sub_self, add_zero]

theorem Aext_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) : Aext A' t s = A' s := by
  funext ω
  simp only [Aext, clampT_of_mem hs, max_eq_right hs.2, sub_self, add_zero]

theorem Mext_of_nonpos {s : ℝ} (hs : s ≤ 0) : Mext W M' t s = 0 := by
  funext ω
  simp only [Mext, clampT_of_nonpos h.ht hs, min_eq_left (hs.trans h.ht), sub_self, add_zero,
    h.zeroM ω, Pi.zero_apply]

theorem Aext_of_nonpos {s : ℝ} (hs : s ≤ 0) : Aext A' t s = 0 := by
  funext ω
  simp only [Aext, clampT_of_nonpos h.ht hs, max_eq_right (hs.trans h.ht), sub_self, add_zero,
    h.zeroA ω, Pi.zero_apply]

theorem Mext_of_ge {s : ℝ} (hs : t ≤ s) (ω : Ω₂) :
    Mext W M' t s ω = M' t ω + (bw W s ω - bw W t ω) := by
  simp only [Mext, clampT_of_ge h.ht hs, min_eq_right hs]

theorem Aext_of_ge {s : ℝ} (hs : t ≤ s) (ω : Ω₂) : Aext A' t s ω = A' t ω + (s - t) := by
  simp only [Aext, clampT_of_ge h.ht hs, max_eq_left hs]

theorem integrable_A' : Integrable (A' t) P₂ := by
  have h1 : MemLp (M' t) 2 P₂ := h.memLp t ⟨h.ht, le_rfl⟩
  have : A' t = fun ω => M' t ω ^ 2 - (M' t ω ^ 2 - A' t ω) := by funext ω; ring
  rw [this]
  exact h1.integrable_sq.sub (h.qmart.integrable t)

theorem memLp_bw (s : ℝ) : MemLp (bw W s) 2 P₂ := h.bf.memLp_two_coord_real s 0

theorem memLp_Mext (s : ℝ) : MemLp (Mext W M' t s) 2 P₂ :=
  (h.memLp _ (clampT_mem h.ht s)).add ((h.memLp_bw s).sub (h.memLp_bw (min s t)))

theorem integrable_Aext (s : ℝ) : Integrable (Aext A' t s) P₂ := by
  have h1 : Integrable (A' (clampT t s)) P₂ := by
    have h2 : MemLp (M' (clampT t s)) 2 P₂ := h.memLp _ (clampT_mem h.ht s)
    have : A' (clampT t s) = fun ω => M' (clampT t s) ω ^ 2 -
        (M' (clampT t s) ω ^ 2 - A' (clampT t s) ω) := by funext ω; ring
    rw [this]
    exact h2.integrable_sq.sub (h.qmart.integrable _)
  exact h1.add (integrable_const _)

end ExtData

end Extension2

section Extension3

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝒢 : Filtration ℝ m₂} {W : ℝ≥0 → Ω₂ → Fin 1 → ℝ} {t : ℝ} {M' A' : ℝ → Ω₂ → ℝ}

theorem condExp_add_eq_of_condExp_zero {𝒜 : MeasurableSpace Ω₂} (h𝒜 : 𝒜 ≤ m₂) {a b : Ω₂ → ℝ}
    (ha : StronglyMeasurable[𝒜] a) (hai : Integrable a P₂) (hbi : Integrable b P₂)
    (hb : P₂[b | 𝒜] =ᵐ[P₂] 0) : P₂[fun ω => a ω + b ω | 𝒜] =ᵐ[P₂] a := by
  have e1 := condExp_add hai hbi 𝒜 (μ := P₂)
  have e2 : P₂[a | 𝒜] = a := condExp_of_stronglyMeasurable h𝒜 ha hai
  filter_upwards [e1, hb] with ω h1 h2
  rw [show (fun ω => a ω + b ω) = a + b from rfl, h1, Pi.add_apply, e2, h2]
  simp

theorem condExp_add_zero {𝒜 : MeasurableSpace Ω₂} {b₁ b₂ : Ω₂ → ℝ}
    (hb₁i : Integrable b₁ P₂) (hb₂i : Integrable b₂ P₂)
    (h₁ : P₂[b₁ | 𝒜] =ᵐ[P₂] 0) (h₂ : P₂[b₂ | 𝒜] =ᵐ[P₂] 0) :
    P₂[fun ω => b₁ ω + b₂ ω | 𝒜] =ᵐ[P₂] 0 := by
  have e1 := condExp_add hb₁i hb₂i 𝒜 (μ := P₂)
  filter_upwards [e1, h₁, h₂] with ω h1 h2 h3
  rw [show (fun ω => b₁ ω + b₂ ω) = b₁ + b₂ from rfl, h1, Pi.add_apply, h2, h3]
  simp

namespace ExtData

variable (h : ExtData P₂ 𝒢 W t M' A')
include h

/-- Brownian increment after time `s`. -/
theorem condExp_bw_incr {s r : ℝ} (hsr : s ≤ r) :
    P₂[fun ω => bw W r ω - bw W s ω | 𝒢 s] =ᵐ[P₂] 0 :=
  h.bf.condExp_incr_real hsr 0

theorem integrable_bw_incr {s r : ℝ} (_hsr : s ≤ r) :
    Integrable (fun ω => bw W r ω - bw W s ω) P₂ :=
  ((h.memLp_bw r).sub (h.memLp_bw s)).integrable one_le_two

theorem martingale_Mext : Martingale (Mext W M' t) 𝒢 P₂ := by
  refine martingale_of_pieces (c := t) (fun s => h.stronglyMeasurable_Mext s)
    (fun s hs ω => by rw [h.Mext_of_nonpos hs]; rfl) ?_ ?_
  · intro s r hs hsr hrt
    rw [h.Mext_of_mem ⟨hs.trans hsr, hrt⟩, h.Mext_of_mem ⟨hs, hsr.trans hrt⟩]
    exact h.mart.2 s r hsr
  · intro s r hts hsr
    have hsd : Mext W M' t r = fun ω => Mext W M' t s ω + (bw W r ω - bw W s ω) := by
      funext ω
      rw [h.Mext_of_ge (hts.trans hsr), h.Mext_of_ge hts]; ring
    rw [hsd]
    exact condExp_add_eq_of_condExp_zero (𝒢.le s) (h.stronglyMeasurable_Mext s)
      ((h.memLp_Mext s).integrable one_le_two) (h.integrable_bw_incr hsr) (h.condExp_bw_incr hsr)

theorem martingale_Qext :
    Martingale (fun s ω => Mext W M' t s ω ^ 2 - Aext A' t s ω) 𝒢 P₂ := by
  refine martingale_of_pieces (c := t)
    (fun s => ((h.stronglyMeasurable_Mext s).pow 2).sub (h.adapted_Aext s).stronglyMeasurable)
    (fun s hs ω => ?_) ?_ ?_
  · simp only [h.Mext_of_nonpos hs, h.Aext_of_nonpos hs, Pi.zero_apply]; ring
  · intro s r hs hsr hrt
    have e : ∀ u ∈ Set.Icc (0 : ℝ) t, (fun ω => Mext W M' t u ω ^ 2 - Aext A' t u ω) =
        fun ω => M' u ω ^ 2 - A' u ω := fun u hu => by
      rw [h.Mext_of_mem hu, h.Aext_of_mem hu]
    rw [e r ⟨hs.trans hsr, hrt⟩, e s ⟨hs, hsr.trans hrt⟩]
    exact h.qmart.2 s r hsr
  · intro s r hts hsr
    have htr : t ≤ r := hts.trans hsr
    have hs0 : 0 ≤ s := h.ht.trans hts
    set D : Ω₂ → ℝ := fun ω => bw W r ω - bw W s ω with hD
    have hDL2 : MemLp D 2 P₂ := (h.memLp_bw r).sub (h.memLp_bw s)
    have hMs := h.memLp_Mext s
    have hQs : StronglyMeasurable[𝒢 s] (fun ω => Mext W M' t s ω ^ 2 - Aext A' t s ω) :=
      ((h.stronglyMeasurable_Mext s).pow 2).sub (h.adapted_Aext s).stronglyMeasurable
    have hQsi : Integrable (fun ω => Mext W M' t s ω ^ 2 - Aext A' t s ω) P₂ :=
      hMs.integrable_sq.sub (h.integrable_Aext s)
    have hsd : (fun ω => Mext W M' t r ω ^ 2 - Aext A' t r ω) =
        fun ω => (Mext W M' t s ω ^ 2 - Aext A' t s ω) +
          (2 * (Mext W M' t s ω * D ω) + (D ω ^ 2 - (r - s))) := by
      funext ω
      have h1 : Mext W M' t r ω = Mext W M' t s ω + D ω := by
        rw [h.Mext_of_ge htr, h.Mext_of_ge hts, hD]; ring
      have h2 : Aext A' t r ω = Aext A' t s ω + (r - s) := by
        rw [h.Aext_of_ge htr, h.Aext_of_ge hts]; ring
      rw [h1, h2]; ring
    rw [hsd]
    have hMD : Integrable (fun ω => Mext W M' t s ω * D ω) P₂ := hMs.integrable_mul hDL2
    have hb1i : Integrable (fun ω => 2 * (Mext W M' t s ω * D ω)) P₂ := hMD.const_mul 2
    have hb2i : Integrable (fun ω => D ω ^ 2 - (r - s)) P₂ :=
      hDL2.integrable_sq.sub (integrable_const _)
    refine condExp_add_eq_of_condExp_zero (𝒢.le s) hQs hQsi (hb1i.add hb2i)
      (condExp_add_zero hb1i hb2i ?_ ?_)
    · have h1 := condExp_smul (μ := P₂) (2 : ℝ) (fun ω => Mext W M' t s ω * D ω) (𝒢 s)
      have h2 : P₂[fun ω => Mext W M' t s ω * D ω | 𝒢 s] =ᵐ[P₂] 0 :=
        h.bf.condExp_mul_incr_real hsr 0 (h.stronglyMeasurable_Mext s) hMD
      filter_upwards [h1, h2] with ω h1 h2
      have h1' : P₂[fun ω => 2 * (Mext W M' t s ω * D ω) | 𝒢 s] ω =
          2 * P₂[fun ω => Mext W M' t s ω * D ω | 𝒢 s] ω := h1
      rw [h1', h2]; simp
    · have h1 := condExp_sub hDL2.integrable_sq (integrable_const (r - s)) (𝒢 s) (μ := P₂)
      have h2 := h.bf.condExp_incr_sq_real hsr 0
      have h3 : P₂[fun _ : Ω₂ => r - s | 𝒢 s] = fun _ => r - s := condExp_const (𝒢.le s) _
      filter_upwards [h1, h2] with ω h1 h2
      rw [show (fun ω => D ω ^ 2 - (r - s)) = (fun ω => D ω ^ 2) - fun _ => r - s from rfl, h1,
        Pi.sub_apply, h3]
      have : P₂[fun ω => D ω ^ 2 | 𝒢 s] ω = max r 0 - max s 0 := h2
      rw [this, max_eq_left (hs0.trans hsr), max_eq_left hs0]
      simp

end ExtData

end Extension3

section Extension4

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝒢 : Filtration ℝ m₂} {W : ℝ≥0 → Ω₂ → Fin 1 → ℝ} {t : ℝ} {M' A' : ℝ → Ω₂ → ℝ}

namespace ExtData

variable (h : ExtData P₂ 𝒢 W t M' A')
include h

theorem continuous_bw (ω : Ω₂) : Continuous fun s => bw W s ω :=
  (continuous_apply 0).comp (continuous_ofNNRealTime W ω (h.bf.cont ω))

theorem continuous_Mext (ω : Ω₂) : Continuous fun s => Mext W M' t s ω :=
  ((h.contM ω).comp_continuous (continuous_clampT t) (fun s => clampT_mem h.ht s)).add
    ((h.continuous_bw ω).sub ((h.continuous_bw ω).comp (continuous_id.min continuous_const)))

theorem continuous_Aext (ω : Ω₂) : Continuous fun s => Aext A' t s ω :=
  ((h.contA ω).comp_continuous (continuous_clampT t) (fun s => clampT_mem h.ht s)).add
    ((continuous_id.max continuous_const).sub continuous_const)

theorem monotone_Aext (ω : Ω₂) : Monotone fun s => Aext A' t s ω := fun a b hab =>
  add_le_add (h.monoA ω (clampT_mem h.ht a) (clampT_mem h.ht b) (monotone_clampT t hab))
    (sub_le_sub_right (max_le_max hab le_rfl) _)

theorem tendsto_Aext (ω : Ω₂) : Tendsto (fun s => Aext A' t s ω) atTop atTop := by
  have h1 : Tendsto (fun s : ℝ => s - t) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t) tendsto_id
  refine tendsto_atTop_mono (fun s => ?_) h1
  have h2 : A' 0 ω ≤ A' (clampT t s) ω :=
    h.monoA ω ⟨le_rfl, h.ht⟩ (clampT_mem h.ht s) (clampT_mem h.ht s).1
  have h3 : s ≤ max s t := le_max_left _ _
  have h4 := h.zeroA ω
  simp only [Aext]
  linarith

theorem tcData : TCData P₂ 𝒢 (Mext W M' t) (Aext A' t) where
  mart := h.martingale_Mext
  cont := h.continuous_Mext
  zero := fun ω => by
    rw [show Mext W M' t 0 = M' 0 from h.Mext_of_mem ⟨le_rfl, h.ht⟩]; exact h.zeroM ω
  memLp := h.memLp_Mext
  compensator := h.martingale_Qext
  adapted := h.adapted_Aext
  contA := h.continuous_Aext
  monoA := h.monotone_Aext
  zeroA := fun ω => by
    rw [show Aext A' t 0 = A' 0 from h.Aext_of_mem ⟨le_rfl, h.ht⟩]; exact h.zeroA ω
  topA := h.tendsto_Aext

end ExtData

end Extension4

/-! ### B.7.2 The time change and Lévy's characterisation -/

section Core

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝒢 : Filtration ℝ m₂} {W : ℝ≥0 → Ω₂ → Fin 1 → ℝ} {t : ℝ} {M' A' : ℝ → Ω₂ → ℝ}

theorem ExtData.brownian_core (h : ExtData P₂ 𝒢 W t M' A') :
    ∃ (ℱ' : Filtration ℝ m₂) (β : ℝ≥0 → Ω₂ → Fin 1 → ℝ), IsBrownianFiltration P₂ ℱ' β ∧
      (∀ τ ∈ Set.Icc 0 t, IsStoppingTime ℱ' fun ω => ((max (A' τ ω) 0 : ℝ) : WithTop ℝ)) ∧
      (∀ᵐ ω ∂P₂, ∀ τ ∈ Set.Icc 0 t, M' τ ω = β (Real.toNNReal (A' τ ω)) ω 0) := by
  classical
  have hT := h.tcData
  obtain ⟨hcomp, hadapt, hzero, hcont, hmart, hqv⟩ := timeChange_levy_hypotheses hT
  set ℱ' := timeChangedFiltration P₂ 𝒢 (Aext A' t) hT.adapted hT.contA with hℱ'
  set β0 : ℝ → Ω₂ → ℝ := tcProcess (Mext W M' t) (Aext A' t) with hβ0
  have hβ0max : ∀ u ω, β0 (max u 0) ω = β0 u ω := fun u ω => by
    simp only [hβ0, tcProcess, levelTimeR_max_zero (hT.zeroA ω)]
  have hmeas : ∀ u : ℝ≥0, Measurable (fun ω => β0 u ω) := fun u => hT.measurable_tcProcess (u : ℝ)
  have hcont' : ∀ᵐ ω ∂P₂, Continuous fun u : ℝ≥0 => β0 u ω :=
    hcont.mono fun ω hω => hω.comp NNReal.continuous_coe
  obtain ⟨Y, hYm, hYc, hYae⟩ := exists_continuous_modification P₂ (fun (u : ℝ≥0) ω => β0 u ω) hmeas hcont'
  set βs : ℝ≥0 → Ω₂ → ℝ := fun u ω => Y u ω - Y 0 ω with hβs
  have hY0 : ∀ᵐ ω ∂P₂, Y 0 ω = 0 := by
    filter_upwards [hYae] with ω hω
    rw [hω 0]; exact hzero ω
  have hβsae : ∀ᵐ ω ∂P₂, ∀ u : ℝ≥0, βs u ω = β0 u ω := by
    filter_upwards [hYae, hY0] with ω h1 h2 u
    simp only [hβs, h1 u, h2, sub_zero]
  have hβsm : ∀ u, Measurable (βs u) := fun u => (hYm u).sub (hYm 0)
  -- real-time version
  have hβsR : ∀ u : ℝ, (fun ω => ofNNRealTime βs u ω) =ᵐ[P₂] β0 u := by
    intro u
    filter_upwards [hβsae] with ω hω
    simp only [ofNNRealTime_apply]
    rw [hω, ← hβ0max u ω]
    congr 1
  have hβsad : ∀ u : ℝ, Measurable[ℱ' u] (fun ω => ofNNRealTime βs u ω) := fun u =>
    hcomp.measurable_of_ae_eq u (hadapt u)
      ((hβsm _)) (hβsR u).symm
  refine ⟨ℱ', fun u ω _ => βs u ω, ?_, ?_, ?_⟩
  · refine levy_characterization P₂ ℱ' hcomp (fun u ω _ => βs u ω) ?_ ?_ ?_ ?_ ?_
    · intro u
      have hb := hβsad (u : ℝ)
      letI : MeasurableSpace Ω₂ := ℱ' u
      exact measurable_pi_iff.2 fun _ => by simpa using hb
    · intro ω; funext k; simp [hβs]
    · intro ω; exact continuous_pi fun _ => (hYc ω).sub continuous_const
    · intro k
      refine martingale_congr_ae hmart (fun u => (hβsad u).stronglyMeasurable) hβsR
    · intro k l
      have hkl : k = l := Subsingleton.elim k l
      subst hkl
      refine martingale_congr_ae hqv (fun u => ?_) (fun u => ?_)
      · simp only [ite_true]
        exact (((hβsad u).mul (hβsad u)).sub measurable_const).stronglyMeasurable
      · simp only [ite_true]
        filter_upwards [hβsR u] with ω hω
        simp only [ofNNRealTime_apply] at hω ⊢
        rw [hω]
  · intro τ hτ
    have e := h.Aext_of_mem hτ
    have := isStoppingTime_max_level (P := P₂) (𝒢 := 𝒢) (A := Aext A' t) (hA := hT.adapted)
      (hc := hT.contA) hT.monoA hT.zeroA τ hτ.1
    rw [e] at this
    exact this
  · filter_upwards [hT.ae_const_on_const_of_qv_real, hβsae] with ω hconst hβω τ hτ
    have hAτ : Aext A' t τ ω = A' τ ω := by rw [h.Aext_of_mem hτ]
    have hu0 : 0 ≤ A' τ ω := by
      have h3 : A' 0 ω ≤ A' τ ω := h.monoA ω ⟨le_rfl, h.ht⟩ hτ hτ.1
      rwa [h.zeroA ω] at h3
    set S := levelTimeR (Aext A' t) (A' τ ω) ω with hS
    have hS0 : 0 ≤ S := levelTimeR_nonneg (hT.topA ω) _
    have hSτ : S ≤ τ := levelTimeR_le_of_le (hT.topA ω) (hT.contA ω) (hT.monoA ω) hτ.1
      (le_of_eq (by rw [hAτ]))
    have hAS : Aext A' t S ω = A' τ ω := by
      rw [hS, hT.A_levelTimeR_max' ω, max_eq_left hu0]
    have hc := hconst S τ hS0 hSτ (by rw [hAS, hAτ]) τ ⟨hSτ, le_rfl⟩
    have h1 : β0 (A' τ ω) ω = Mext W M' t S ω := rfl
    have h2 : M' τ ω = Mext W M' t τ ω := by rw [h.Mext_of_mem hτ]
    have h3 : βs (Real.toNNReal (A' τ ω)) ω = β0 (A' τ ω) ω := by
      rw [hβω, hβ0, show ((Real.toNNReal (A' τ ω) : ℝ≥0) : ℝ) = A' τ ω from
        Real.coe_toNNReal _ hu0]
    show M' τ ω = βs (Real.toNNReal (A' τ ω)) ω
    rw [h3, h1, h2, hc]

end Core

/-! ### B.7.3 Instantiation on the enlarged space -/

section Instantiate

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {t : ℝ} {M A : ℝ → Ω → ℝ}

/-- The measure on the enlarged space. -/
abbrev ddsMeasure (hc : CleanData P ℱ t M A) : Measure (DDSSpace t) :=
  (P.map (codeMap hc)).prod (Measure.pi fun _ : Fin 1 => wienerMeasure)

theorem exists_extData (hc : CleanData P ℱ t M A) (ht : 0 ≤ t) :
    ∃ (W : ℝ≥0 → DDSSpace t → Fin 1 → ℝ) (hW : ∀ r, Measurable (W r)),
      ExtData (ddsMeasure hc) (ddsFiltration t (ddsMeasure hc) W hW) W t
        (fun τ p => (p.1.1 τ).1) (fun τ p => (p.1.1 τ).2) := by
  obtain ⟨W, hW, hW0, hWc, hind, hBF⟩ :=
    exists_enlargement_indep (Fin 1) (CodedPath t) (P.map (codeMap hc))
  refine ⟨W, hW, ?_⟩
  set P' := ddsMeasure hc with hP'
  have hfst : MeasurePreserving (Prod.fst : DDSSpace t → CodedPath t) P' (P.map (codeMap hc)) :=
    measurePreserving_fst
  have hcomplete : IsCompleteFiltration P' (ddsFiltration t P' W hW) := by
    intro u S hS hP
    have h1 : MeasurableSet[nullSets P'] S := MeasurableSpace.measurableSet_generateFrom ⟨hS, hP⟩
    exact (le_sup_right : nullSets P' ≤ _) S h1
  have hgm : ∀ τ, StronglyMeasurable[pathPart t τ] (fun p : DDSSpace t => (p.1.1 τ).1) :=
    fun τ => ((measurable_fst.comp (measurable_pathEval_sigma (t := t) (le_refl τ))).comp
      (comap_measurable (Prod.fst : DDSSpace t → CodedPath t))).stronglyMeasurable
  have hgmA : ∀ τ, Measurable[pathPart t τ] (fun p : DDSSpace t => (p.1.1 τ).2) :=
    fun τ => (measurable_snd.comp (measurable_pathEval_sigma (t := t) (le_refl τ))).comp
      (comap_measurable (Prod.fst : DDSSpace t → CodedPath t))
  refine
    { bf := IsBrownianFiltration.of_le_of_adapted hBF (fun u => ddsFiltration_le_generated u)
        hcomplete (fun u => ?_)
      ht := ht
      mart := ?_
      qmart := ?_
      memLp := ?_
      adaptedA := fun τ => (hgmA τ).mono (pathPart_le_ddsFiltration τ) le_rfl
      zeroM := fun p => congrArg Prod.fst p.1.2.2.2
      zeroA := fun p => congrArg Prod.snd p.1.2.2.2
      contM := fun p => continuous_fst.comp_continuousOn p.1.2.1
      contA := fun p => continuous_snd.comp_continuousOn p.1.2.1
      monoA := fun p => p.1.2.2.1 }
  · exact (Measurable.of_comap_le ((le_iSup₂_of_le u le_rfl le_rfl :
      MeasurableSpace.comap (W u) inferInstance ≤ wienerPart t W (u : ℝ)).trans
        (wienerPart_le_ddsFiltration (P' := P') (hW := hW) (u : ℝ))))
  · exact martingale_coded hc (fun _ x => x.1) (fun _ => measurable_fst) hc.mart hW hind
  · exact martingale_coded hc (fun _ x => x.1 ^ 2 - x.2)
      (fun _ => (measurable_fst.pow_const 2).sub measurable_snd) hc.qmart hW hind
  · intro τ hτ
    have h1 : MemLp (fun x : CodedPath t => (x.1 τ).1) 2 (P.map (codeMap hc)) := by
      refine (memLp_map_measure_iff ?_ (measurable_codeMap hc).aemeasurable).2 (hc.memLp τ hτ)
      exact (measurable_fst.comp (measurable_pathEval τ)).aestronglyMeasurable
    exact h1.comp_measurePreserving hfst

end Instantiate

/-! ### B.8 Finite-dimensional laws and the assembly -/

section Assembly

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {t : ℝ} {M A : ℝ → Ω → ℝ}

theorem law_coded (hc : CleanData P ℱ t M A) (n : ℕ) (ts : Fin n → ℝ) :
    law (ddsMeasure hc) (fun (p : DDSSpace t) (i : Fin n) => ((p.1.1 (ts i)).1, (p.1.1 (ts i)).2)) =
      law P (fun ω (i : Fin n) => (M (ts i) ω, A (ts i) ω)) := by
  set F : CodedPath t → Fin n → ℝ × ℝ := fun x i => x.1 (ts i) with hF
  have hFm : Measurable F := Measurable.of_eval fun i => measurable_pathEval (ts i)
  have hfst : MeasurePreserving (Prod.fst : DDSSpace t → CodedPath t) (ddsMeasure hc)
      (P.map (codeMap hc)) := measurePreserving_fst
  have e1 : (fun (p : DDSSpace t) (i : Fin n) => ((p.1.1 (ts i)).1, (p.1.1 (ts i)).2)) =
      F ∘ Prod.fst := rfl
  have e2 : (fun ω (i : Fin n) => (M (ts i) ω, A (ts i) ω)) = F ∘ codeMap hc := rfl
  unfold law
  rw [e1, e2, ← Measure.map_map hFm measurable_fst, hfst.map_eq,
    Measure.map_map hFm (measurable_codeMap hc)]

end Assembly

/-- The core of `dambis_dubins_schwarz`, with the additional information that `M'_τ` and `A'_τ`
are measurable (used for `dds_coupling_proof`). -/
theorem dambis_dubins_schwarz_core (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ) (hM : IsContSqMartingale P ℱ t M)
    (hA : IsQuadraticVariation P ℱ t M A) (hint : Integrable (A t) P) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (ℱ' : Filtration ℝ mΩ') (β : ℝ≥0 → Ω' → Fin 1 → ℝ) (M' A' : ℝ → Ω' → ℝ),
      IsBrownianFiltration P' ℱ' β ∧
      (∀ (n : ℕ) (ts : Fin n → ℝ),
        law P' (fun ω' => fun i => (M' (ts i) ω', A' (ts i) ω')) =
          law P (fun ω => fun i => (M (ts i) ω, A (ts i) ω))) ∧
      (∀ τ ∈ Set.Icc 0 t, IsStoppingTime ℱ' fun ω' => ((max (A' τ ω') 0 : ℝ) : WithTop ℝ)) ∧
      (∀ᵐ ω' ∂P', ∀ τ ∈ Set.Icc 0 t, M' τ ω' = β (Real.toNNReal (A' τ ω')) ω' 0) ∧
      (∀ τ, Measurable (M' τ)) ∧ (∀ τ, Measurable (A' τ)) := by
  obtain ⟨M₁, A₁, hc, hM₁, hA₁⟩ := exists_clean hM hA hint
  obtain ⟨W, hW, hext⟩ := exists_extData hc ht
  obtain ⟨ℱ', β, hβ, hstop, hid⟩ := hext.brownian_core
  refine ⟨DDSSpace t, inferInstance, ddsMeasure hc, inferInstance, ℱ', β,
    fun τ p => (p.1.1 τ).1, fun τ p => (p.1.1 τ).2, hβ, ?_, hstop, hid,
    fun τ => measurable_fst.comp ((measurable_pathEval τ).comp measurable_fst),
    fun τ => measurable_snd.comp ((measurable_pathEval τ).comp measurable_fst)⟩
  intro n ts
  rw [law_coded hc n ts]
  unfold law
  refine Measure.map_congr ?_
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin n, M₁ (ts i) ω = M (ts i) ω ∧ A₁ (ts i) ω = A (ts i) ω :=
    ae_all_iff.2 fun i => Filter.Eventually.and (hM₁ (ts i)) (hA₁ (ts i))
  filter_upwards [hall] with ω hω
  funext i
  simp only [(hω i).1, (hω i).2]

/-- **Dambis–Dubins–Schwarz** (M L10529): for a continuous square-integrable martingale `M` on
`[0, t]` with quadratic variation `A` (in the sense of `HRS/Prob/CLT.lean`) and `E A_t < ∞`, there
are a probability space `Ω'`, a complete filtration `ℱ'` with a one-dimensional Brownian motion
`β` (`IsBrownianFiltration`, `ι = Fin 1`), and processes `M', A'` on `Ω'` such that
`(M', A')` has the finite-dimensional laws of `(M, A)`, each `A'_τ` (`τ ≤ t`) is an `ℱ'`-stopping
time, and `M'_τ = β_{A'_τ}` for all `τ ∈ [0, t]` a.s.  (Proof route: extend `M` beyond `t` by an
independent Brownian motion on `Ω' = Ω × C`, time-change by `T_u = inf {τ : A_τ > u}`, prove that
`M` is constant on the intervals of constancy of `A`, use continuous-time optional sampling for
`M` and `M² - A`, and conclude by `levy_characterization`.) -/
theorem dambis_dubins_schwarz (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ) (hM : IsContSqMartingale P ℱ t M)
    (hA : IsQuadraticVariation P ℱ t M A) (hint : Integrable (A t) P) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (ℱ' : Filtration ℝ mΩ') (β : ℝ≥0 → Ω' → Fin 1 → ℝ) (M' A' : ℝ → Ω' → ℝ),
      IsBrownianFiltration P' ℱ' β ∧
      (∀ (n : ℕ) (ts : Fin n → ℝ),
        law P' (fun ω' => fun i => (M' (ts i) ω', A' (ts i) ω')) =
          law P (fun ω => fun i => (M (ts i) ω, A (ts i) ω))) ∧
      (∀ τ ∈ Set.Icc 0 t, IsStoppingTime ℱ' fun ω' => ((max (A' τ ω') 0 : ℝ) : WithTop ℝ)) ∧
      (∀ᵐ ω' ∂P', ∀ τ ∈ Set.Icc 0 t, M' τ ω' = β (Real.toNNReal (A' τ ω')) ω' 0) := by
  obtain ⟨Ω', mΩ', P', hP', ℱ', β, M', A', h1, h2, h3, h4, -, -⟩ :=
    dambis_dubins_schwarz_core P ℱ t ht M A hM hA hint
  exact ⟨Ω', mΩ', P', hP', ℱ', β, M', A', h1, h2, h3, h4⟩

/-! ### B.9 The coupling form (`dds_coupling`) -/

theorem toNNReal_max_zero (x : ℝ) : Real.toNNReal (max x 0) = Real.toNNReal x :=
  NNReal.eq (by rw [Real.coe_toNNReal', Real.coe_toNNReal', max_assoc, max_self])

/-- `dds_coupling` (`HRS/Prob/CLT.lean`), proved here because `CLT.lean` is upstream of the
stochastic files. -/
theorem dds_coupling_strong {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) (v : ℝ) (hv : 0 ≤ v) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (M' A' : Ω' → ℝ) (β : ℝ≥0 → Ω' → ℝ),
      Measurable M' ∧ Measurable A' ∧
      ProbabilityTheory.IsBrownianReal β P' ∧
      law P' (fun ω' => (M' ω', A' ω')) = law P (fun ω => (M t ω, A t ω)) ∧
      (∀ᵐ ω' ∂P', M' ω' = β (Real.toNNReal (A' ω')) ω') ∧
      law P' (β (Real.toNNReal v)) = gaussianLaw v ∧
      ∫⁻ ω', ‖β (Real.toNNReal (A' ω')) ω' - β (Real.toNNReal v) ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (∫ ω, |A t ω - v| ∂P) := by
  obtain ⟨Ω', mΩ', P', hP', ℱ', β, M', A', hβ, hlaw, hstop, hid, hM'm, hA'm⟩ :=
    dambis_dubins_schwarz_core P ℱ t ht M A hM hA hint
  have hMm : Measurable (M t) := (hM.martingale.1 t).measurable.mono (ℱ.le t) le_rfl
  have hAm : Measurable (A t) := (hA.adapted t).mono (ℱ.le t) le_rfl
  set f : Ω → ℝ × ℝ := fun ω => (M t ω, A t ω) with hf
  set f' : Ω' → ℝ × ℝ := fun ω' => (M' t ω', A' t ω') with hf'
  have hfm : Measurable f := hMm.prodMk hAm
  have hf'm : Measurable f' := (hM'm t).prodMk (hA'm t)
  have hlaw1 : law P' (fun ω' (_ : Fin 1) => (M' t ω', A' t ω')) =
      law P (fun ω (_ : Fin 1) => (M t ω, A t ω)) := hlaw 1 (fun _ => t)
  have hFm : Measurable (fun ω (_ : Fin 1) => (M t ω, A t ω)) := Measurable.of_eval fun _ => hfm
  have hF'm : Measurable (fun ω' (_ : Fin 1) => (M' t ω', A' t ω')) :=
    Measurable.of_eval fun _ => hf'm
  have hf'ae : AEMeasurable f' P' := hf'm.aemeasurable
  have hpair : law P' f' = law P f := by
    have e := congrArg (Measure.map (fun F : Fin 1 → ℝ × ℝ => F 0)) hlaw1
    unfold law at e ⊢
    rw [Measure.map_map (measurable_pi_apply 0) hF'm,
      Measure.map_map (measurable_pi_apply 0) hFm] at e
    exact e
  have hpush : ∀ g : ℝ × ℝ → ℝ, Measurable g →
      ∫ ω', g (f' ω') ∂P' = ∫ ω, g (f ω) ∂P := by
    intro g hg
    have h1 := integral_map (μ := P') hf'ae hg.aestronglyMeasurable
    have h2 := integral_map (μ := P) hfm.aemeasurable hg.aestronglyMeasurable
    unfold law at hpair
    rw [← h1, ← h2, hpair]
  have hintg : ∀ g : ℝ × ℝ → ℝ, Measurable g → Integrable (fun ω => g (f ω)) P →
      Integrable (fun ω' => g (f' ω')) P' := by
    intro g hg hgi
    have h1 : Integrable g (law P f) :=
      (integrable_map_measure hg.aestronglyMeasurable hfm.aemeasurable).2 hgi
    rw [← hpair] at h1
    exact (integrable_map_measure hg.aestronglyMeasurable hf'ae).1 h1
  have hAnn : ∀ᵐ ω ∂P, 0 ≤ A t ω := by
    filter_upwards [hA.zero, hA.mono] with ω h0 hm
    have h1 : A 0 ω ≤ A t ω := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    rwa [h0] at h1
  have hSint : Integrable (fun ω' => max (A' t ω') 0) P' :=
    hintg (fun p => max p.2 0) (measurable_snd.max measurable_const) hint.pos_part
  have hbound := brownian_stopped_L2_bound hβ 0 (fun ω' => max (A' t ω') 0)
    (fun _ => le_max_right _ _) (hstop t ⟨ht, le_rfl⟩) hSint v hv
  refine ⟨Ω', mΩ', P', hP', M' t, A' t, fun u ω' => β u ω' 0, hM'm t, hA'm t,
    hβ.isBrownianReal 0, hpair, ?_, ?_, ?_⟩
  · filter_upwards [hid] with ω' h
    exact h t ⟨ht, le_rfl⟩
  · exact (hβ.hasLaw_coord (Real.toNNReal v) 0).map_eq
  · simp_rw [toNNReal_max_zero] at hbound
    refine hbound.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have h1 := hpush (fun p => |max p.2 0 - v|)
      ((measurable_snd.max measurable_const).sub measurable_const).abs
    refine h1.trans (integral_congr_ae ?_)
    filter_upwards [hAnn] with ω hω
    simp only [hf, max_eq_left hω]

/-- `dds_coupling` (`HRS/Prob/DDSCoupling.lean`): `dds_coupling_strong` without the measurability
conjuncts. -/
theorem dds_coupling_proof {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) (v : ℝ) (hv : 0 ≤ v) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (M' A' : Ω' → ℝ) (β : ℝ≥0 → Ω' → ℝ),
      ProbabilityTheory.IsBrownianReal β P' ∧
      law P' (fun ω' => (M' ω', A' ω')) = law P (fun ω => (M t ω, A t ω)) ∧
      (∀ᵐ ω' ∂P', M' ω' = β (Real.toNNReal (A' ω')) ω') ∧
      law P' (β (Real.toNNReal v)) = gaussianLaw v ∧
      ∫⁻ ω', ‖β (Real.toNNReal (A' ω')) ω' - β (Real.toNNReal v) ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (∫ ω, |A t ω - v| ∂P) := by
  obtain ⟨Ω', m, P', hP', M', A', β, -, -, h⟩ := dds_coupling_strong P ℱ t ht M A hM hA hint v hv
  exact ⟨Ω', m, P', hP', M', A', β, h⟩

/-- The `W₂` bound of Lemma A.19 `M:B:lem:dds` (`dds_wasserstein_bound` in
`HRS/Prob/DDSCoupling.lean`): `W₂(Law(M_t), N(0,v)) ≤ (E|[M]_t - v|)^{1/2}`, from the coupling
`(M', β_v)` on the enlarged space. -/
theorem dds_wasserstein_bound_proof {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (M A : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hint : Integrable (A t) P) (v : ℝ) (hv : 0 ≤ v) :
    wassersteinE 2 (law P (M t)) (gaussianLaw v) ≤
      ENNReal.ofReal (Real.sqrt (∫ ω, |A t ω - v| ∂P)) := by
  obtain ⟨Ω', m, P', hP', M', A', β, hMm, hAm, hB, hlaw, hid, hgauss, hbd⟩ :=
    dds_coupling_strong P ℱ t ht M A hM hA hint v hv
  have hMt : Measurable (M t) := (hM.martingale.1 t).measurable.mono (ℱ.le t) le_rfl
  have hAt : Measurable (A t) := (hA.adapted t).mono (ℱ.le t) le_rfl
  have hl1 : law P' M' = law P (M t) := by
    have e := congrArg (Measure.map Prod.fst) hlaw
    unfold law at e ⊢
    rwa [Measure.map_map measurable_fst (hMm.prodMk hAm),
      Measure.map_map measurable_fst (hMt.prodMk hAt)] at e
  have hY : AEMeasurable (β (Real.toNNReal v)) P' := hB.toIsPreBrownianReal.aemeasurable _
  have hc := wassersteinE_le_of_coupling P' 2 (by norm_num) M' (β (Real.toNNReal v))
    hMm.aemeasurable hY
  rw [hl1, hgauss] at hc
  refine hc.trans ?_
  have h2 : ∫⁻ ω', ENNReal.ofReal (‖M' ω' - β (Real.toNNReal v) ω'‖ ^ (2 : ℝ)) ∂P' ≤
      ENNReal.ofReal (∫ ω, |A t ω - v| ∂P) := by
    refine le_trans (le_of_eq ?_) hbd
    refine lintegral_congr_ae ?_
    filter_upwards [hid] with ω h
    rw [h, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    norm_cast
  calc (∫⁻ ω', ENNReal.ofReal (‖M' ω' - β (Real.toNNReal v) ω'‖ ^ (2 : ℝ)) ∂P') ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (∫ ω, |A t ω - v| ∂P)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (∫ ω, |A t ω - v| ∂P)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => abs_nonneg _) (by norm_num),
          Real.sqrt_eq_rpow, one_div]

/-! `dds_coupling` (now in `HRS/Prob/DDSCoupling.lean`, downstream of this file) is proved there
as `dds_coupling_proof`; its type is checked by that proof term. -/

end HRS
