import HRS.Main.GFB4Aux13

/-!
# GFB4, part 14: independence lemmas for the initial enlargement `Ω × E_γ`, `P ⊗ κ`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS

/-- Sets of `m ⊔ nullSets P` are a.e. equal to sets of `m`. -/
theorem gfb4_sup_null_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (m : MeasurableSpace Ω)
    {A : Set Ω} (hA : MeasurableSet[m ⊔ HRS.nullSets P] A) : ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B := by
  let mm : MeasurableSpace Ω :=
    { MeasurableSet' := fun A => ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B
      measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, Filter.EventuallyEq.refl _ _⟩
      measurableSet_compl := fun A ⟨B, hB, hAB⟩ => ⟨Bᶜ, @MeasurableSet.compl Ω B m hB, hAB.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose B hB hfB using hf
        exact ⟨⋃ i, B i, @MeasurableSet.iUnion Ω ℕ m _ B hB, Filter.EventuallyEqSet.countable_iUnion hfB⟩ }
  have h1 : m ≤ mm := fun A hA => ⟨A, hA, Filter.EventuallyEq.refl _ _⟩
  have h2 : HRS.nullSets P ≤ mm := by
    refine MeasurableSpace.generateFrom_le fun A hA => ⟨∅, @MeasurableSet.empty Ω m, ?_⟩
    exact (ae_eq_empty.2 hA.2)
  have h3 : m ⊔ HRS.nullSets P ≤ mm := sup_le h1 h2
  exact h3 A hA

theorem gfb4_indep_null {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) {a m : MeasurableSpace Ω}
    (h : Indep a m P) : Indep a (m ⊔ HRS.nullSets P) P := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 h1 h2
  obtain ⟨B, hB, hAB⟩ := gfb4_sup_null_ae P m h2
  rw [measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ t1) hAB), measure_congr hAB]
  exact h t1 B h1 hB

/-- The key independence: the new randomness `η'` is drawn from a kernel depending on `ξ ∈ ℱ_0` only. -/
theorem gfb4_indep_core {Ω E X B : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    {mX : MeasurableSpace X} {mB : MeasurableSpace B} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {s : ℝ} (hs : 0 ≤ s) {ξ : Ω → X} (hξ : Measurable[ℱ 0] ξ)
    (K : Kernel X E) [IsMarkovKernel K] (Δ : Ω → B) (hΔ : Measurable Δ)
    (hind : Indep (MeasurableSpace.comap Δ mB) (ℱ s) P) :
    Indep (MeasurableSpace.comap (fun w : Ω × E => Δ w.1) mB) (@Prod.instMeasurableSpace Ω E (ℱ s) mE)
      (P ⊗ₘ (K.comap ξ (hξ.mono (ℱ.le 0) le_rfl))) := by
  set κ : Kernel Ω E := K.comap ξ (hξ.mono (ℱ.le 0) le_rfl) with hκ
  have hξs : Measurable[ℱ s] ξ := hξ.mono (ℱ.mono hs) le_rfl
  have hprod : @Prod.instMeasurableSpace Ω E (ℱ s) mE ≤ @Prod.instMeasurableSpace Ω E mΩ mE :=
    sup_le_sup (MeasurableSpace.comap_mono (ℱ.le s)) le_rfl
  refine IndepSets.indep (m1 := MeasurableSpace.comap (fun w : Ω × E => Δ w.1) mB)
    (m2 := @Prod.instMeasurableSpace Ω E (ℱ s) mE)
    (p1 := {S | MeasurableSet[MeasurableSpace.comap (fun w : Ω × E => Δ w.1) mB] S})
    (p2 := Set.image2 (fun x1 x2 => x1 ×ˢ x2) {A | MeasurableSet[ℱ s] A} {t | MeasurableSet[mE] t})
    ?_ hprod ?_ ?_ ?_ ?_ ?_
  · exact (hΔ.comp measurable_fst).comap_le
  · exact @MeasurableSpace.isPiSystem_measurableSet _ (MeasurableSpace.comap (fun w : Ω × E => Δ w.1) mB)
  · exact @isPiSystem_prod Ω E (ℱ s) mE
  · exact (@MeasurableSpace.generateFrom_measurableSet _ (MeasurableSpace.comap (fun w : Ω × E => Δ w.1) mB)).symm
  · exact (@generateFrom_prod Ω E (ℱ s) mE).symm
  · rw [IndepSets_iff]
    intro S T hS hT
    obtain ⟨A, hA, B, hB, rfl⟩ := hT
    obtain ⟨U, hU, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hS
    set C₀ : Set Ω := Δ ⁻¹' U with hC₀
    have hC₀m : MeasurableSet C₀ := hΔ hU
    have hC₀c : MeasurableSet[MeasurableSpace.comap Δ mB] C₀ := ⟨U, hU, rfl⟩
    have hAm : MeasurableSet A := ℱ.le s _ hA
    have hBm : MeasurableSet B := hB
    have e1 : (fun w : Ω × E => Δ w.1) ⁻¹' U ∩ (A ×ˢ B) = (C₀ ∩ A) ×ˢ B := by
      ext w; simp [hC₀, Set.mem_prod, and_assoc]
    have e2 : (fun w : Ω × E => Δ w.1) ⁻¹' U = C₀ ×ˢ (Set.univ : Set E) := by
      ext w; simp [hC₀]
    rw [e1, Measure.compProd_apply_prod (hC₀m.inter hAm) hBm]
    rw [e2, Measure.compProd_apply_prod hC₀m MeasurableSet.univ,
      Measure.compProd_apply_prod hAm hBm]
    have hκ1 : ∀ ω, κ ω Set.univ = 1 := fun ω => measure_univ
    simp_rw [hκ1]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]
    have hg : Measurable[ℱ s] (A.indicator (fun ω => κ ω B)) := by
      refine Measurable.indicator ?_ hA
      exact (Kernel.measurable_coe K hBm).comp hξs
    have hf : Measurable[MeasurableSpace.comap Δ mB] (C₀.indicator (fun _ : Ω => (1 : ℝ≥0∞))) :=
      Measurable.indicator measurable_const hC₀c
    have key := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (Mf := MeasurableSpace.comap Δ mB) (Mg := ℱ s) (mΩ := mΩ) (μ := P) hΔ.comap_le (ℱ.le s) hind hf hg
    have hpt : ∀ ω, C₀.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω * A.indicator (fun ω => κ ω B) ω =
        (C₀ ∩ A).indicator (fun ω => κ ω B) ω := by
      intro ω
      by_cases h1 : ω ∈ C₀ <;> by_cases h2 : ω ∈ A <;> simp [h1, h2, Set.indicator]
    simp_rw [hpt] at key
    rw [lintegral_indicator (hC₀m.inter hAm), lintegral_indicator hAm, lintegral_indicator hC₀m] at key
    simpa [Measure.restrict_apply, hC₀m] using key

end HRS.GF
