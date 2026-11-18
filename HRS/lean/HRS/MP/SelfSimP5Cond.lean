import HRS.MP.SelfSimP5Spec
import HRS.MP.SelfSimP1CepaUniq

/-!
# MPP5B (2): conditioning an ordered solution on the order class of `Y₀`, `ss5_cond_solution`

`HRS.MP.SelfSimP5Impl.ss5_cond_solution_proof` has the statement of `HRS.MP.SelfSimP5.ss5_cond_solution`.
The new filtration is `ℱ' t = ℱ t ⊔ nullSets Q` for `Q = P[· | A_σ]`, `A_σ = Y₀⁻¹(cone σ) ∈ ℱ 0`
(template `h5_cond_filtered_proof`, `HRS/MC/CepH5FFilt.lean`, whose auxiliary lemmas are copied with the prefix `ss5d_`).
The ordering permutation of `SSOrdered` is forced to be `σ` on `A_σ` by `ssp1c_perm_unique`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP5Impl

section Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

set_option warn.classDefReducibility false in
/-- The σ-algebra of measurable sets that are `Q`-a.e. equal to a set of `m`. -/
def ss5d_aeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' G := MeasurableSet[mΩ] G ∧ ∃ F, MeasurableSet[m] F ∧ G =ᵐ[Q] F
  measurableSet_empty := ⟨@MeasurableSet.empty _ mΩ, ∅, @MeasurableSet.empty _ m, Filter.EventuallyEq.rfl⟩
  measurableSet_compl := by
    rintro G ⟨hG, F, hF, hGF⟩
    exact ⟨@MeasurableSet.compl _ _ mΩ hG, Fᶜ, @MeasurableSet.compl _ _ m hF, hGF.compl⟩
  measurableSet_iUnion := by
    intro f hf
    choose hfm F hF hfF using hf
    refine ⟨@MeasurableSet.iUnion _ _ mΩ _ _ hfm, ⋃ i, F i, @MeasurableSet.iUnion _ _ m _ _ hF, ?_⟩
    exact Filter.EventuallyEqSet.countable_iUnion hfF

theorem ss5d_le_aeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    m ≤ ss5d_aeSigma Q m := fun s hs => ⟨hm s hs, s, hs, Filter.EventuallyEq.rfl⟩

theorem ss5d_nullSets_le_aeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) :
    nullSets Q ≤ ss5d_aeSigma Q m := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨hs, h0⟩
  refine ⟨hs, ∅, @MeasurableSet.empty _ m, ?_⟩
  exact (ae_eq_empty.2 h0)

variable {P : Measure Ω}

theorem ss5d_cond_value_of_indep [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) {E : Set Ω} (hE : MeasurableSet[m1] E) :
    ProbabilityTheory.cond P A E = P E := by
  have hAm : MeasurableSet[mΩ] A := h2 _ hA
  rw [ProbabilityTheory.cond_apply hAm, Set.inter_comm,
    ((Indep_iff _ _ _).1 hind) E A hE hA, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel hPA (measure_ne_top P A), mul_one]

theorem ss5d_cond_inter_of_indep [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) {E F : Set Ω} (hE : MeasurableSet[m1] E) (hF : MeasurableSet[m2] F) :
    ProbabilityTheory.cond P A (E ∩ F) =
      ProbabilityTheory.cond P A E * ProbabilityTheory.cond P A F := by
  have hAm : MeasurableSet[mΩ] A := h2 _ hA
  rw [ss5d_cond_value_of_indep h1 h2 hind hA hPA hE, ProbabilityTheory.cond_apply hAm,
    ProbabilityTheory.cond_apply hAm]
  have : A ∩ (E ∩ F) = E ∩ (A ∩ F) := by ext; simp [and_left_comm]
  rw [this, ((Indep_iff _ _ _).1 hind) E (A ∩ F) hE (hA.inter hF)]
  ring

theorem ss5d_indep_cond_sup_null [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) :
    Indep m1 (m2 ⊔ nullSets (ProbabilityTheory.cond P A)) (ProbabilityTheory.cond P A) := by
  set Q := ProbabilityTheory.cond P A with hQ
  have hle : m2 ⊔ nullSets Q ≤ ss5d_aeSigma Q m2 :=
    sup_le (ss5d_le_aeSigma Q m2 h2) (ss5d_nullSets_le_aeSigma Q m2)
  refine indep_of_indep_of_le_right ?_ hle
  rw [Indep_iff]
  intro E G hE hG
  obtain ⟨hGm, F, hF, hGF⟩ := hG
  have e1 : E ∩ G =ᵐ[Q] E ∩ F := Filter.EventuallyEq.inter Filter.EventuallyEq.rfl hGF
  rw [measure_congr e1, measure_congr hGF, ss5d_cond_inter_of_indep h1 h2 hind hA hPA hE hF]

end Aux

/-- The cone is a measurable set of configurations. -/
theorem ss5d_cone_measurable {N : ℕ} (σ : Equiv.Perm (Fin N)) : MeasurableSet (ss5_cone σ) := by
  have hm : ∀ i : Fin N, Measurable fun ξ : EucConfig 1 N => ξ i 0 := fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).measurable).comp (measurable_pi_apply i)
  have : ss5_cone σ = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l),
      {ξ : EucConfig 1 N | ξ (σ k) 0 < ξ (σ l) 0} := by
    ext ξ; simp [ss5_cone]
  rw [this]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hm (σ k)) (hm (σ l))

/-- Filtered-solution part of `ss5_cond_solution`: augment `ℱ` by the `Q`-null sets. -/
theorem ss5d_cond_filtered {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hF : IsWholeFilteredSolution P ℱ W' W Y) {A : Set Ω} (hA0 : MeasurableSet[ℱ 0] A)
    (hPA : P A ≠ 0) :
    ∃ ℱ' : Filtration ℝ mΩ, IsWholeFilteredSolution (ProbabilityTheory.cond P A) ℱ' W' W Y := by
  set Q : Measure Ω := ProbabilityTheory.cond P A with hQ
  have hAs : ∀ s : ℝ≥0, MeasurableSet[ℱ (s : ℝ)] A := fun s => ℱ.mono (by simp) _ hA0
  let ℱ' : Filtration ℝ mΩ :=
    { seq := fun t => ℱ t ⊔ nullSets Q
      mono' := fun a b h => sup_le_sup_right (ℱ.mono h) _
      le' := fun t => sup_le (ℱ.le t) (nullSets_le Q) }
  have hle : ∀ t, ℱ t ≤ ℱ' t := fun t => le_sup_left
  have hincr : ∀ s t : ℝ≥0, Measurable fun ω => W' t ω - W' s ω := fun s t =>
    ((hF.brownian.adapted t).mono (ℱ.le _) le_rfl).sub ((hF.brownian.adapted s).mono (ℱ.le _) le_rfl)
  refine ⟨ℱ', ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t s hs h0
    exact (le_sup_right : nullSets Q ≤ ℱ t ⊔ nullSets Q) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hs, h0⟩)
  · intro t
    exact (hF.brownian.adapted t).mono (hle _) le_rfl
  · exact hF.brownian.zero
  · exact hF.brownian.cont
  · intro s t hst
    exact ss5d_indep_cond_sup_null (m1 := MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
      (m2 := ℱ s) (hincr s t).comap_le (ℱ.le _) (hF.brownian.indep_incr s t hst) (hAs s) hPA
  · intro s t hst
    refine ⟨(hincr s t).aemeasurable, ?_⟩
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply (hincr s t) hE]
    have := ss5d_cond_value_of_indep (P := P) (m1 := MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
      (m2 := ℱ s) (hincr s t).comap_le (ℱ.le _) (hF.brownian.indep_incr s t hst) (hAs s) hPA
      (E := (fun ω => W' t ω - W' s ω) ⁻¹' E) ⟨E, hE, rfl⟩
    rw [this, ← Measure.map_apply (hincr s t) hE, (hF.brownian.gaussian_incr s t hst).map_eq]
  · exact ProbabilityTheory.cond_absolutelyContinuous.ae_le hF.coords
  · intro t
    exact (hF.adapted t).mono (hle _) le_rfl
  · intro i
    refine (hF.progressive i).mono ?_ le_rfl
    exact sup_le_sup_left (MeasurableSpace.comap_mono (hle i)) _

theorem ss5_cond_solution_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol P invβ (ssDrift 1 0 N) S ℱ W' W Y) (hord : SSOrdered P S Y)
    (σ : Equiv.Perm (Fin N)) (hA : P (Y 0 ⁻¹' ss5_cone σ) ≠ 0) :
    ∃ ℱ' : Filtration ℝ mΩ,
      SSAddSol (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) invβ (ssDrift 1 0 N) S ℱ' W' W Y ∧
      (∀ᵐ ζ ∂(ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)), ∀ t : ℝ≥0, (t : ℝ) ≤ S →
        ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0) ∧
      (∀ᵐ ζ ∂(ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)), Y 0 ζ ∈ ss5_cone σ) := by
  set A : Set Ω := Y 0 ⁻¹' ss5_cone σ with hAdef
  set Q : Measure Ω := ProbabilityTheory.cond P A with hQ
  have hY0 : Measurable[ℱ 0] (Y 0) := by
    have h := hY.filtered.adapted 0
    rwa [NNReal.coe_zero] at h
  have hA0 : MeasurableSet[ℱ 0] A := hY0 (ss5d_cone_measurable σ)
  have hAm : MeasurableSet A := ℱ.le 0 _ hA0
  have hQP : Q ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hAQ : ∀ᵐ ζ ∂Q, Y 0 ζ ∈ ss5_cone σ := ProbabilityTheory.ae_cond_mem hAm
  obtain ⟨ℱ', hF'⟩ := ss5d_cond_filtered hY.filtered hA0 hA
  refine ⟨ℱ', ⟨hF', hY.cont, hQP.ae_le hY.init_distinct, hQP.ae_le hY.eqn,
    hQP.ae_le hY.occupation⟩, ?_, hAQ⟩
  obtain ⟨π, -, hπ⟩ := hord
  have h0S : ((0 : ℝ≥0) : ℝ) ≤ S := by simpa using hS.le
  filter_upwards [hAQ, hQP.ae_le hπ, hQP.ae_le hY.init_distinct] with ζ hζ hπζ hdist
  have hσ : ∀ k k' : Fin N, k ≤ k' → Y 0 ζ (σ k) 0 ≤ Y 0 ζ (σ k') 0 := by
    intro k k' hkk'
    rcases hkk'.lt_or_eq with h | h
    · exact (hζ k k' h).le
    · rw [h]
  have hπ0 : ∀ k k' : Fin N, k ≤ k' → Y 0 ζ (π ζ k) 0 ≤ Y 0 ζ (π ζ k') 0 :=
    fun k k' hkk' => hπζ 0 h0S 0 k k' hkk'
  have hpe : π ζ = σ := HRS.MP.SelfSimP1.ssp1c_perm_unique hdist hπ0 hσ
  intro t ht k k' hkk'
  have := hπζ t ht 0 k k' hkk'
  rwa [hpe] at this

example := (@ss5_cond_solution_proof : type_of% @HRS.MP.SelfSimP5.ss5_cond_solution)

end HRS.MP.SelfSimP5Impl
