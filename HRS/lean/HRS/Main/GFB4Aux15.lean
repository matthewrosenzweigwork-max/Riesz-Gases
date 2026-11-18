import HRS.Main.GFB4Aux14

/-!
# GFB4, part 15: `gf_init_enlargement` with the link `X₀ = X 0` a.s.

`gf_init_enlargement` as stated in `GFSpec3` is false (`X₀` is not linked to the filtered solution `X`; ISSUES "GFB4"); it is proved
here with the extra hypothesis `hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω` (which holds in the use, `IsStrongSolution.init`).  The enlargement is
`Ω' = Ω × E_γ`, `P' = P ⊗ κ`, `κ ω = condDistrib η₀ (X 0) P (X 0 ω)`, `η' = snd`, `ℱ'_t = (ℱ_t ⊗ borel) ⊔ nullSets`.  (`hind` is not needed: `η'` is drawn from a kernel depending on `X 0 ∈ ℱ_0` only.)

Counterexample sketch to the unrepaired statement: `ℱ_t = σ(U) ∨ σ(W_s, s ≤ t) ∨ null`, `U` a fair bit independent of `W`, `X t = const`,
`X₀ = c_{U xor 1[W_1 > 0]}`, `η₀ = e · 1[U xor 1[W_1 > 0]]`: `(X₀, η₀)` is independent of `W`, but any enlargement with `η'` `ℱ'_0`-measurable
and `Law (X₀ ∘ π, η') = Law (X₀, η₀)` makes `1[W_1 > 0] ∘ π = 1_{U∘π} xor 1_{η' = e}` `ℱ'_0`-measurable (completeness), contradicting
`W_1 ⟂ ℱ'_0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform

variable {d : ℕ}

/-- The filtration `ℱ'_t = (ℱ_t ⊗ ℬ(E)) ⊔ nullSets P'` on `Ω × E`. -/
def gfb4_initFil {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} (P' : Measure (Ω × E))
    (ℱ : Filtration ℝ mΩ) : Filtration ℝ (@Prod.instMeasurableSpace Ω E mΩ mE) where
  seq t := (@Prod.instMeasurableSpace Ω E (ℱ t) mE) ⊔ HRS.nullSets P'
  mono' := fun s t h => sup_le_sup_right
    (sup_le_sup (MeasurableSpace.comap_mono (ℱ.mono h)) le_rfl) _
  le' := fun t => sup_le (sup_le_sup (MeasurableSpace.comap_mono (ℱ.le t)) le_rfl)
    (HRS.nullSets_le P')

/-- The joint law of `(ξ, η')` on the enlargement is that of `(ξ, η₀)`. -/
theorem gfb4_init_law {Ω E X : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E] [mX : MeasurableSpace X]
    [StandardBorelSpace E] [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → X}
    (hξ : Measurable ξ) {η₀ : Ω → E} (hη : Measurable η₀) :
    (P ⊗ₘ ((condDistrib η₀ ξ P).comap ξ hξ)).map (fun w : Ω × E => (ξ w.1, w.2)) =
      P.map (fun ω => (ξ ω, η₀ ω)) := by
  rw [← compProd_map_condDistrib hξ.aemeasurable hη.aemeasurable]
  have hf : Measurable (fun w : Ω × E => (ξ w.1, w.2)) := (hξ.comp measurable_fst).prodMk measurable_snd
  refine ext_of_generate_finite
    (Set.image2 (fun x1 x2 => x1 ×ˢ x2) {s | MeasurableSet s} {t | MeasurableSet t}) generateFrom_prod.symm
    isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    have hpre : (fun w : Ω × E => (ξ w.1, w.2)) ⁻¹' (A ×ˢ B) = (ξ ⁻¹' A) ×ˢ B := by
      ext w; simp
    rw [Measure.map_apply hf (hA.prod hB), hpre, Measure.compProd_apply_prod (hξ hA) hB,
      Measure.compProd_apply_prod hA hB, setLIntegral_map hA (Kernel.measurable_coe _ hB) hξ]
    rfl
  · have hf' : (fun w : Ω × E => (ξ w.1, w.2)) ⁻¹' Set.univ = Set.univ := rfl
    rw [Measure.map_apply hf MeasurableSet.univ, hf']
    have := Measure.compProd_apply_prod (μ := P.map ξ) (κ := condDistrib η₀ ξ P) MeasurableSet.univ MeasurableSet.univ
    simp only [Set.univ_prod_univ] at this
    rw [this]
    have h2 := Measure.compProd_apply_prod (μ := P) (κ := (condDistrib η₀ ξ P).comap ξ hξ)
      MeasurableSet.univ MeasurableSet.univ
    simp only [Set.univ_prod_univ] at h2
    rw [h2]
    simp

theorem gfb4_init_enlargement (S : GeneralSetup d) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (hη : Measurable η₀)
    (hind : IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (η' : Ω' → NegSobolev d (S.γ : ℝ)),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsFilteredSolution P' ℱ' (fun t ω' k => W' t (π ω') k) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      Measurable[ℱ' 0] η' ∧
      P'.map (fun ω' => (X₀ (π ω'), η' ω')) = P.map (fun ω => (X₀ ω, η₀ ω)) := by
  classical
  have hX0ℱ : Measurable[ℱ 0] (X 0) := hF.adapted 0
  have hX0m : Measurable (X 0) := hX0ℱ.mono (ℱ.le 0) le_rfl
  set K : Kernel (Config d N) (NegSobolev d (S.γ : ℝ)) := condDistrib η₀ (X 0) P with hK
  set κ : Kernel Ω (NegSobolev d (S.γ : ℝ)) := K.comap (X 0) hX0m with hκ
  set P' : Measure (Ω × NegSobolev d (S.γ : ℝ)) := P ⊗ₘ κ with hP'
  have hπ : MeasurePreserving (Prod.fst : Ω × NegSobolev d (S.γ : ℝ) → Ω) P' P :=
    ⟨measurable_fst, Measure.fst_compProd P κ⟩
  have hπ' : ∀ t : ℝ, Measurable[gfb4_initFil P' ℱ t, ℱ t] (Prod.fst : Ω × NegSobolev d (S.γ : ℝ) → Ω) :=
    fun t => Measurable.of_comap_le (le_sup_left.trans' (le_sup_left (a := MeasurableSpace.comap Prod.fst (ℱ t))))
  refine ⟨Ω × NegSobolev d (S.γ : ℝ), inferInstance, P', inferInstance, Prod.fst, hπ, gfb4_initFil P' ℱ,
    Prod.snd, ?_, ?_, ?_, ?_⟩
  · intro τ
    exact le_sup_left.trans' (le_sup_left (a := MeasurableSpace.comap Prod.fst (ℱ τ)))
  · have hΔm : ∀ s t : ℝ≥0, Measurable (fun ω => W' t ω - W' s ω) := fun s t =>
      ((hF.brownian.adapted t).mono (ℱ.le _) le_rfl).sub ((hF.brownian.adapted s).mono (ℱ.le _) le_rfl)
    have hbr : IsBrownianFiltration P' (gfb4_initFil P' ℱ) (fun t ω' k => W' t (Prod.fst ω') k) :=
      { complete := fun t A hA hA0 =>
          (le_sup_right : HRS.nullSets P' ≤ _) _ (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩)
        adapted := fun t => (hF.brownian.adapted t).comp (hπ' t)
        zero := fun ω => hF.brownian.zero _
        cont := fun ω => hF.brownian.cont _
        indep_incr := fun s t hst => by
          have h1 := gfb4_indep_core P ℱ (s := (s : ℝ)) s.2 hX0ℱ K (fun ω => W' t ω - W' s ω)
            (hΔm s t) (hF.brownian.indep_incr s t hst)
          exact gfb4_indep_null P' h1
        gaussian_incr := fun s t hst => by
          have h := hF.brownian.gaussian_incr s t hst
          refine ⟨((hΔm s t).comp measurable_fst).aemeasurable, ?_⟩
          rw [show (fun ω' : Ω × NegSobolev d (S.γ : ℝ) => W' t (Prod.fst ω') - W' s (Prod.fst ω')) =
            (fun ω => W' t ω - W' s ω) ∘ Prod.fst from rfl, ← Measure.map_map (hΔm s t) measurable_fst,
            hπ.map_eq]
          exact h.map_eq }
    refine ⟨hbr, ?_, ?_, ?_⟩
    · filter_upwards [hπ.quasiMeasurePreserving.ae hF.coords] with w hw t i j
      exact hw t i j
    · intro t
      exact (hF.adapted t).comp (hπ' t)
    · intro i
      have h := hF.progressive i
      exact h.comp (measurable_fst.prodMk ((hπ' i).comp measurable_snd))
  · exact Measurable.of_comap_le
      (le_sup_left.trans' (le_sup_right (b := MeasurableSpace.comap Prod.snd inferInstance)
        (a := MeasurableSpace.comap Prod.fst (ℱ 0))))
  · have h1 : P'.map (fun w : Ω × NegSobolev d (S.γ : ℝ) => (X 0 w.1, w.2)) = P.map (fun ω => (X 0 ω, η₀ ω)) :=
      gfb4_init_law P hX0m hη
    have h2 : P.map (fun ω => (X 0 ω, η₀ ω)) = P.map (fun ω => (X₀ ω, η₀ ω)) := by
      refine Measure.map_congr ?_
      filter_upwards [hX0] with ω hω
      rw [hω]
    have h3 : P'.map (fun w : Ω × NegSobolev d (S.γ : ℝ) => (X₀ w.1, w.2)) =
        P'.map (fun w : Ω × NegSobolev d (S.γ : ℝ) => (X 0 w.1, w.2)) := by
      refine Measure.map_congr ?_
      filter_upwards [hπ.quasiMeasurePreserving.ae hX0] with w hw
      rw [hw]
    show P'.map (fun w : Ω × NegSobolev d (S.γ : ℝ) => (X₀ w.1, w.2)) = _
    rw [h3, h1, h2]

end HRS.GF
