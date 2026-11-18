import HRS.Stochastic.Bridge
import HRS.Whole.Dynamics

/-!
# S.A.28 packet P1, generic prelude (`SelfSimP1Base`)

Branch-independent ingredients for `ss_P1_filtered_version` (`HRS/MP/SelfSimSpec.lean`), shared by the
collision-free branch (`SelfSimP1Free`) and the Cépa-Lépingle branch.

* `ssp1_base`: from `IsVectorBrownian P W`, `Measurable X₀`, `X₀ ⫫ W`, a Brownian filtration `ℱ` (the augmented
  filtration of `(X₀, W')`, complete) with the continuous coordinates `W'` of `W`; `X₀` and `W'_s` (`s ≤ t`) are
  `ℱ t`-measurable.
* `ssp1_exists_measurable_good`, `ssp1_measurableSet_of_null_compl`: an a.e. property holds on a measurable set of
  full measure, which belongs to every `ℱ t` of a complete filtration.
* the freezing device `ssp1_freeze T G Y t ζ = Y (min t T) ζ` on `G`, `0` off `G`: adaptedness for all `t`,
  everywhere continuity, progressive measurability.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.SelfSimP1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d N : ℕ}

/-- The Brownian filtration of `P` carrying `X₀` and the continuous coordinates `W'` of `W`:
`ℱ t = σ(X₀) ⊔ σ(W'_s, s ≤ t) ⊔ nullSets P`. -/
theorem ssp1_base (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    {E : Type*} [MeasurableSpace E] (X₀ : Ω → E) (hX₀ : Measurable X₀)
    (hind : IndepFun X₀ (fun ζ => fun t => W t ζ) P) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsBrownianFiltration P ℱ W' ∧ IsCompleteFiltration P ℱ ∧
      (∀ᵐ ζ ∂P, ∀ t i j, W' t ζ (i, j) = W t ζ i j) ∧
      (∀ t : ℝ, Measurable[ℱ t] X₀) ∧
      (∀ s : ℝ≥0, ∀ t : ℝ, (s : ℝ) ≤ t → Measurable[ℱ t] (W' s)) ∧
      (∀ t : ℝ, ∀ s : ℝ, s ≤ t → ℱ s ≤ ℱ t) := by
  obtain ⟨W', hW'm, hae, hBF, hX₀ℱ⟩ := exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  refine ⟨generatedFiltration P X₀ hX₀ W' hW'm, W', hBF, hBF.complete, hae, hX₀ℱ,
    fun s t hst => generatedFiltration_measurable_W P X₀ hX₀ W' hW'm s t hst,
    fun t s hst => (generatedFiltration P X₀ hX₀ W' hW'm).mono hst⟩

/-- The filtration of `ssp1_base` is exactly the generated augmented one (for the Cépa branch's use of
`σ(X₀, W'|[0,t]) ⊆ ℱ t`). -/
theorem ssp1_base_gen (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    {E : Type*} [MeasurableSpace E] (X₀ : Ω → E) (hX₀ : Measurable X₀)
    (hind : IndepFun X₀ (fun ζ => fun t => W t ζ) P) :
    ∃ (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hW'm : ∀ t, Measurable (W' t)),
      IsBrownianFiltration P (generatedFiltration P X₀ hX₀ W' hW'm) W' ∧
      (∀ᵐ ζ ∂P, ∀ t i j, W' t ζ (i, j) = W t ζ i j) ∧
      (∀ t : ℝ, Measurable[generatedFiltration P X₀ hX₀ W' hW'm t] X₀) := by
  obtain ⟨W', hW'm, hae, hBF, hX₀ℱ⟩ := exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  exact ⟨W', hW'm, hBF, hae, hX₀ℱ⟩

/-- An a.e. property holds on a measurable set of full measure. -/
theorem ssp1_exists_measurable_good (P : Measure Ω) {p : Ω → Prop} (h : ∀ᵐ ζ ∂P, p ζ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ζ ∈ G, p ζ := by
  have h0 : P {ζ | ¬ p ζ} = 0 := ae_iff.1 h
  refine ⟨(toMeasurable P {ζ | ¬ p ζ})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact h0
  · intro ζ hζ
    by_contra hp
    exact hζ (subset_toMeasurable P {ζ | ¬ p ζ} hp)

/-- A measurable set with null complement belongs to every `ℱ t` of a complete filtration. -/
theorem ssp1_measurableSet_of_null_compl {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    (hℱ : IsCompleteFiltration P ℱ) {G : Set Ω} (hG : MeasurableSet G) (hP : P Gᶜ = 0) (t : ℝ) :
    MeasurableSet[ℱ t] G := by
  have := hℱ t Gᶜ hG.compl hP
  simpa using this.compl

/-! ### The freezing device -/

open Classical in
/-- `X'_t := Y_{min t T}` on `G`, `0` off `G`. -/
def ssp1_freeze {E : Type*} [Zero E] (T : ℝ) (G : Set Ω) (Y : ℝ → Ω → E) (t : ℝ≥0) (ζ : Ω) : E :=
  if ζ ∈ G then Y (min (t : ℝ) T) ζ else 0

theorem ssp1_freeze_of_le {E : Type*} [Zero E] {T : ℝ} {G : Set Ω} {Y : ℝ → Ω → E} {t : ℝ≥0}
    (ht : (t : ℝ) ≤ T) {ζ : Ω} (hζ : ζ ∈ G) : ssp1_freeze T G Y t ζ = Y t ζ := by
  simp [ssp1_freeze, hζ, min_eq_left ht]

theorem ssp1_freeze_of_notMem {E : Type*} [Zero E] {T : ℝ} {G : Set Ω} {Y : ℝ → Ω → E} {t : ℝ≥0}
    {ζ : Ω} (hζ : ζ ∉ G) : ssp1_freeze T G Y t ζ = 0 := by
  simp [ssp1_freeze, hζ]

/-- Freezing preserves adaptedness at every time. -/
theorem ssp1_freeze_adapted {E : Type*} [Zero E] [MeasurableSpace E] {ℱ : Filtration ℝ mΩ}
    {T : ℝ} {G : Set Ω} {Y : ℝ → Ω → E} (hG : ∀ t : ℝ, MeasurableSet[ℱ t] G)
    (hY : ∀ t : ℝ, Measurable[ℱ t] (Y t)) (t : ℝ≥0) :
    Measurable[ℱ t] (ssp1_freeze T G Y t) := by
  have h1 : Measurable[ℱ t] (Y (min (t : ℝ) T)) :=
    Measurable.mono (hY _) (ℱ.mono (min_le_left _ _)) le_rfl
  have h2 : MeasurableSet[ℱ t] G := hG t
  exact Measurable.ite h2 h1 measurable_const

/-- Everywhere continuity of the frozen process. -/
theorem ssp1_freeze_continuous {E : Type*} [Zero E] [TopologicalSpace E] {T : ℝ} (hT : 0 ≤ T)
    {G : Set Ω} {Y : ℝ → Ω → E} (hY : ∀ ζ ∈ G, ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T))
    (ζ : Ω) : Continuous fun t : ℝ≥0 => ssp1_freeze T G Y t ζ := by
  by_cases hζ : ζ ∈ G
  · have : (fun t : ℝ≥0 => ssp1_freeze T G Y t ζ) = fun t : ℝ≥0 => Y (min (t : ℝ) T) ζ := by
      funext t; simp [ssp1_freeze, hζ]
    rw [this]
    refine (hY ζ hζ).comp_continuous (NNReal.continuous_coe.min continuous_const) fun t => ?_
    exact ⟨le_min t.2 hT, min_le_right _ _⟩
  · have : (fun t : ℝ≥0 => ssp1_freeze T G Y t ζ) = fun _ => 0 := by
      funext t; exact ssp1_freeze_of_notMem hζ
    rw [this]; exact continuous_const

/-- Progressive measurability = adaptedness + everywhere continuity (the time-`0` value must be measurable for
every `ℱ t`, `t < 0`, since `ofNNRealTime X` is constant on `(-∞, 0]`). -/
theorem ssp1_isProgressive_of_continuous {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [TopologicalSpace.MetrizableSpace E] [BorelSpace E] [SecondCountableTopology E] {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → E} (hX : ∀ t : ℝ≥0, Measurable[ℱ t] (X t))
    (hX0 : ∀ t : ℝ, Measurable[ℱ t] (X 0))
    (hc : ∀ ζ, Continuous fun t : ℝ≥0 => X t ζ) : IsProgressive ℱ (ofNNRealTime X) := by
  refine (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => ?_) (fun ζ => continuous_ofNNRealTime X ζ (hc ζ))).isProgressive
  rcases le_or_gt 0 t with ht | ht
  · have h : Measurable[ℱ t] (X (Real.toNNReal t)) :=
      Measurable.mono (hX _) (ℱ.mono (by rw [Real.coe_toNNReal t ht])) le_rfl
    exact h.stronglyMeasurable
  · have e : Real.toNNReal t = 0 := Real.toNNReal_of_nonpos ht.le
    have h : Measurable[ℱ t] (X (Real.toNNReal t)) := by rw [e]; exact hX0 t
    exact h.stronglyMeasurable

end HRS.MP.SelfSimP1
