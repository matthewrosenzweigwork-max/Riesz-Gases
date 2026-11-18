import HRS.Main.GFB4Aux15
import HRS.MS.GenPathAux39

/-!
# S5.6 packet P7e: the first (initial-data) enlargement for the whole-space particle system
(copy of `T25P.t25p_init_enlargement` for `EucConfig`, `IsWholeFilteredSolution` and an arbitrary target `E`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.GF

variable {d : ℕ}

theorem s56_init_law {Ω E X : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → X} (hξ : Measurable ξ) (K : Kernel X E) [IsMarkovKernel K] :
    (P ⊗ₘ (K.comap ξ hξ)).map (fun w : Ω × E => (ξ w.1, w.2)) = (P.map ξ) ⊗ₘ K := by
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
    have h2 := Measure.compProd_apply_prod (μ := P) (κ := K.comap ξ hξ)
      MeasurableSet.univ MeasurableSet.univ
    have h1 := Measure.compProd_apply_prod (μ := P.map ξ) (κ := K) MeasurableSet.univ MeasurableSet.univ
    simp only [Set.univ_prod_univ] at h1 h2
    rw [h1, h2]
    simp

theorem s56_init_enlargement {E : Type} [mE : MeasurableSpace E] (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (K : Kernel (EucConfig d N) E) [IsMarkovKernel K] :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (η' : Ω' → E),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsWholeFilteredSolution P' ℱ' (fun t ω' k => W' t (π ω') k) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      Measurable[ℱ' 0] η' ∧
      P'.map (fun ω' => (X₀ (π ω'), η' ω')) = (P.map X₀) ⊗ₘ K := by
  classical
  have hX0ℱ : Measurable[ℱ 0] (X 0) := hF.adapted 0
  have hX0m : Measurable (X 0) := hX0ℱ.mono (ℱ.le 0) le_rfl
  set κ : Kernel Ω (E) := K.comap (X 0) hX0m with hκ
  set P' : Measure (Ω × E) := P ⊗ₘ κ with hP'
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) P' P :=
    ⟨measurable_fst, Measure.fst_compProd P κ⟩
  have hπ' : ∀ t : ℝ, Measurable[gfb4_initFil P' ℱ t, ℱ t] (Prod.fst : Ω × E → Ω) :=
    fun t => Measurable.of_comap_le (le_sup_left.trans' (le_sup_left (a := MeasurableSpace.comap Prod.fst (ℱ t))))
  refine ⟨Ω × E, inferInstance, P', inferInstance, Prod.fst, hπ, gfb4_initFil P' ℱ,
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
          rw [show (fun ω' : Ω × E => W' t (Prod.fst ω') - W' s (Prod.fst ω')) =
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
  · have h1 : P'.map (fun w : Ω × E => (X 0 w.1, w.2)) = (P.map (X 0)) ⊗ₘ K :=
      s56_init_law P hX0m K
    have h2 : P.map (X 0) = P.map X₀ := by
      refine Measure.map_congr ?_
      filter_upwards [hX0] with ω hω
      exact hω
    have h3 : P'.map (fun w : Ω × E => (X₀ w.1, w.2)) =
        P'.map (fun w : Ω × E => (X 0 w.1, w.2)) := by
      refine Measure.map_congr ?_
      filter_upwards [hπ.quasiMeasurePreserving.ae hX0] with w hw
      rw [hw]
    show P'.map (fun w : Ω × E => (X₀ w.1, w.2)) = _
    rw [h3, h1, h2]

end HRS.MS.GenPath
