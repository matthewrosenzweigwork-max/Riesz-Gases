import HRS.PDE.MovDAux1

/-!
# MOVD Aux2: conditioning on an event keeps the hypotheses of `MovHyp` (`movT_cond_hyp`)

Route.  `P' = P(·|A)`, `A = (X 0)⁻¹ B ∈ ℱ_0`.  `P' ≪ P`, so all a.s. statements pass to `P'`.  Events of
`σ(path of W)` are independent of `A` (`A =ᵐ X₀⁻¹ B`, `X₀ ⫫ W`), so laws and independence of functions of the path of
`W` are unchanged; increments `W_t - W_s` are independent of `ℱ_s ∋ A`.  The filtration is enlarged by the
`P'`-null sets (`IsCompleteFiltration` requires them).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

section Generic

variable {Ω : Type*}

theorem movd_cond_apply [MeasurableSpace Ω] (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) (S : Set Ω) :
    movT_cond P A S = (P A)⁻¹ * P (S ∩ A) := by
  simp [movT_cond, Measure.smul_apply, Measure.restrict_apply' hA]

theorem movd_cond_ac [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : movT_cond P A ≪ P := by
  unfold movT_cond
  exact (Measure.smul_absolutelyContinuous).trans Measure.restrict_le_self.absolutelyContinuous

theorem movd_cond_eq_of_indep [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) (h0 : P A ≠ 0) {S : Set Ω} (h : P (S ∩ A) = P S * P A) :
    movT_cond P A S = P S := by
  rw [movd_cond_apply P hA, h, mul_comm (P S), ← mul_assoc,
    ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]

theorem movd_cond_map_eq {G : MeasurableSpace Ω} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) (h0 : P A ≠ 0) {β : Type*} [MeasurableSpace β]
    {F : Ω → β} (hF : Measurable[G] F) (hFa : AEMeasurable F P)
    (hG : ∀ S, MeasurableSet[G] S → P (S ∩ A) = P S * P A) :
    (movT_cond P A).map F = P.map F := by
  have hFa' : AEMeasurable F (movT_cond P A) := hFa.mono_ac (movd_cond_ac P A)
  ext E hE
  rw [Measure.map_apply_of_aemeasurable hFa' hE, Measure.map_apply_of_aemeasurable hFa hE]
  exact movd_cond_eq_of_indep P hA h0 (hG _ (hF hE))

theorem movd_cond_iIndepFun {G : MeasurableSpace Ω} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) (h0 : P A ≠ 0) {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {f : ∀ i, Ω → β i} (hf : ∀ i, Measurable[G] (f i))
    (hind : iIndepFun f P) (hG : ∀ S, MeasurableSet[G] S → P (S ∩ A) = P S * P A) :
    iIndepFun f (movT_cond P A) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro S sets hsets
  have hmeas : ∀ i ∈ S, MeasurableSet[G] (f i ⁻¹' sets i) := fun i hi => hf i (hsets i hi)
  have hI : MeasurableSet[G] (⋂ i ∈ S, f i ⁻¹' sets i) :=
    @Finset.measurableSet_biInter Ω ι G _ S hmeas
  rw [movd_cond_eq_of_indep P hA h0 (hG _ hI), hind S hsets]
  exact Finset.prod_congr rfl fun i hi => (movd_cond_eq_of_indep P hA h0 (hG _ (hmeas i hi))).symm

/-- Events of `σ(Z)` are independent of an event a.e. equal to `X₀⁻¹ B`. -/
theorem movd_indep_event [MeasurableSpace Ω] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P : Measure Ω)
    {A : Set Ω} {X₀ : Ω → α} {Z : Ω → β} (hind : IndepFun X₀ Z P) {B : Set α}
    (hB : MeasurableSet B) (hAB : A =ᵐ[P] X₀ ⁻¹' B) :
    ∀ S, MeasurableSet[MeasurableSpace.comap Z inferInstance] S → P (S ∩ A) = P S * P A := by
  intro S hS
  have h1 := (Indep_iff _ _ _).1 hind (X₀ ⁻¹' B) S ⟨B, hB, rfl⟩ hS
  rw [measure_congr (EventuallyEqSet.inter (EventuallyEq.refl _ _) hAB), measure_congr hAB,
    Set.inter_comm, h1, mul_comm]

theorem movd_cond_indepFun [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) (h0 : P A ≠ 0) {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X₀ : Ω → α} {Z : Ω → β} (hind : IndepFun X₀ Z P) {B : Set α}
    (hB : MeasurableSet B) (hAB : A =ᵐ[P] X₀ ⁻¹' B) :
    IndepFun X₀ Z (movT_cond P A) := by
  have hG := movd_indep_event P hind hB hAB
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro s t hs ht
  have e1 : ∀ S : Set Ω, P (S ∩ A) = P (S ∩ X₀ ⁻¹' B) := fun S =>
    measure_congr (EventuallyEqSet.inter (EventuallyEq.refl _ _) hAB)
  have hs' : P (X₀ ⁻¹' s ∩ A) = P (X₀ ⁻¹' (s ∩ B)) := by
    rw [e1, Set.preimage_inter]
  have hst : P ((X₀ ⁻¹' s ∩ Z ⁻¹' t) ∩ A) = P (X₀ ⁻¹' (s ∩ B)) * P (Z ⁻¹' t) := by
    rw [e1, ← hind (s ∩ B) t (hs.inter hB) ht]
    congr 1
    ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hZ : movT_cond P A (Z ⁻¹' t) = P (Z ⁻¹' t) :=
    movd_cond_eq_of_indep P hA h0 (hG _ ⟨t, ht, rfl⟩)
  rw [movd_cond_apply P hA, movd_cond_apply P hA, hZ, hst, hs']
  ring

end Generic

section Filt

variable {Ω : Type*}

/-- `ℱ u ⊔ nullSets P'`. -/
def movd_aug {mΩ : MeasurableSpace Ω} (P' : Measure Ω) (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq u := ℱ u ⊔ nullSets P'
  mono' := fun _ _ h => sup_le_sup_right (ℱ.mono h) _
  le' := fun u => sup_le (ℱ.le u) (nullSets_le P')

theorem movd_aug_complete {mΩ : MeasurableSpace Ω} (P' : Measure Ω) (ℱ : Filtration ℝ mΩ) :
    IsCompleteFiltration P' (movd_aug P' ℱ) := by
  intro t s hs hP
  have h1 : MeasurableSet[nullSets P'] s := MeasurableSpace.measurableSet_generateFrom ⟨hs, hP⟩
  exact (le_sup_right : nullSets P' ≤ ℱ t ⊔ nullSets P') s h1

theorem movd_sup_null_ae {mΩ : MeasurableSpace Ω} (P : Measure Ω) (m : MeasurableSpace Ω)
    {A : Set Ω} (hA : MeasurableSet[m ⊔ nullSets P] A) : ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B := by
  let mm : MeasurableSpace Ω :=
    { MeasurableSet' := fun A => ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B
      measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, Filter.EventuallyEq.refl _ _⟩
      measurableSet_compl := fun A ⟨B, hB, hAB⟩ => ⟨Bᶜ, @MeasurableSet.compl Ω B m hB, hAB.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose B hB hfB using hf
        exact ⟨⋃ i, B i, @MeasurableSet.iUnion Ω ℕ m _ B hB, Filter.EventuallyEqSet.countable_iUnion hfB⟩ }
  have h1 : m ≤ mm := fun A hA => ⟨A, hA, Filter.EventuallyEq.refl _ _⟩
  have h2 : nullSets P ≤ mm := by
    refine MeasurableSpace.generateFrom_le fun A hA => ⟨∅, @MeasurableSet.empty Ω m, ?_⟩
    exact (ae_eq_empty.2 hA.2)
  have h3 : m ⊔ nullSets P ≤ mm := sup_le h1 h2
  exact h3 A hA

theorem movd_indep_null {mΩ : MeasurableSpace Ω} (P : Measure Ω) {a m : MeasurableSpace Ω}
    (h : Indep a m P) : Indep a (m ⊔ nullSets P) P := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 h1 h2
  obtain ⟨B, hB, hAB⟩ := movd_sup_null_ae P m h2
  rw [measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ t1) hAB), measure_congr hAB]
  exact h t1 B h1 hB

/-- Independence of `m1` and `m2` survives conditioning on an event of `m2`. -/
theorem movd_cond_indep {m1 m2 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) (h0 : P A ≠ 0) (hind : Indep m1 m2 P)
    (hAm : MeasurableSet[m2] A) : Indep m1 m2 (movT_cond P A) := by
  rw [Indep_iff]
  intro G F hG hF
  have hPG : movT_cond P A G = P G :=
    movd_cond_eq_of_indep P hA h0 ((Indep_iff _ _ _).1 hind G A hG hAm)
  have hFA : MeasurableSet[m2] (F ∩ A) := @MeasurableSet.inter Ω m2 _ _ hF hAm
  have h1 : P (G ∩ F ∩ A) = P G * P (F ∩ A) := by
    rw [Set.inter_assoc]; exact (Indep_iff _ _ _).1 hind G (F ∩ A) hG hFA
  rw [hPG, movd_cond_apply P hA, movd_cond_apply P hA, h1]
  ring

end Filt

end HRS

end
