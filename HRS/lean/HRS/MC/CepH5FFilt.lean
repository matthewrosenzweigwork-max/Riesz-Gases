import HRS.Dynamics.Setup
import HRS.Stochastic.Filtration

/-!
# Packet F: `h5_cond_filtered_proof`

Proof of the filtered-solution statement under conditioning on an `X₀`-event.  The new filtration is
`ℱ' t = ℱ t ⊔ nullSets Q` for `Q = P[·| X₀ ∈ B]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

set_option warn.classDefReducibility false in
/-- The σ-algebra of measurable sets that are `Q`-a.e. equal to a set of `m`. -/
def fAeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
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

theorem le_fAeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    m ≤ fAeSigma Q m := fun s hs => ⟨hm s hs, s, hs, Filter.EventuallyEq.rfl⟩

theorem nullSets_le_fAeSigma (Q : Measure Ω) (m : MeasurableSpace Ω) :
    nullSets Q ≤ fAeSigma Q m := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨hs, h0⟩
  refine ⟨hs, ∅, @MeasurableSet.empty _ m, ?_⟩
  exact (ae_eq_empty.2 h0)

variable {P : Measure Ω}

theorem cond_value_of_indep [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) {E : Set Ω} (hE : MeasurableSet[m1] E) :
    ProbabilityTheory.cond P A E = P E := by
  have hAm : MeasurableSet[mΩ] A := h2 _ hA
  rw [ProbabilityTheory.cond_apply hAm, Set.inter_comm,
    ((Indep_iff _ _ _).1 hind) E A hE hA, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel hPA (measure_ne_top P A), mul_one]

theorem cond_inter_of_indep [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) {E F : Set Ω} (hE : MeasurableSet[m1] E) (hF : MeasurableSet[m2] F) :
    ProbabilityTheory.cond P A (E ∩ F) =
      ProbabilityTheory.cond P A E * ProbabilityTheory.cond P A F := by
  have hAm : MeasurableSet[mΩ] A := h2 _ hA
  rw [cond_value_of_indep h1 h2 hind hA hPA hE, ProbabilityTheory.cond_apply hAm,
    ProbabilityTheory.cond_apply hAm]
  have : A ∩ (E ∩ F) = E ∩ (A ∩ F) := by ext; simp [and_left_comm]
  rw [this, ((Indep_iff _ _ _).1 hind) E (A ∩ F) hE (hA.inter hF)]
  ring

theorem indep_cond_sup_null [IsProbabilityMeasure P] {m1 m2 : MeasurableSpace Ω} (h1 : m1 ≤ mΩ)
    (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {A : Set Ω} (hA : MeasurableSet[m2] A)
    (hPA : P A ≠ 0) :
    Indep m1 (m2 ⊔ nullSets (ProbabilityTheory.cond P A)) (ProbabilityTheory.cond P A) := by
  set Q := ProbabilityTheory.cond P A with hQ
  have hle : m2 ⊔ nullSets Q ≤ fAeSigma Q m2 :=
    sup_le (le_fAeSigma Q m2 h2) (nullSets_le_fAeSigma Q m2)
  refine indep_of_indep_of_le_right ?_ hle
  rw [Indep_iff]
  intro E G hE hG
  obtain ⟨hGm, F, hF, hGF⟩ := hG
  have e1 : E ∩ G =ᵐ[Q] E ∩ F := Filter.EventuallyEq.inter Filter.EventuallyEq.rfl hGF
  rw [measure_congr e1, measure_congr hGF, cond_inter_of_indep h1 h2 hind hA hPA hE hF]

end Aux

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

theorem h5_cond_filtered_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {X : ℝ≥0 → Ω → Config 1 N} (hinit : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (hF : IsFilteredSolution P ℱ W' W X) {B : Set (Config 1 N)} (hB : MeasurableSet B)
    (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    ∃ ℱ' : Filtration ℝ mΩ, IsFilteredSolution (ProbabilityTheory.cond P (X₀ ⁻¹' B)) ℱ' W' W X := by
  set A : Set Ω := X₀ ⁻¹' B with hAdef
  have hAm : MeasurableSet A := hB.preimage hX₀
  set Q : Measure Ω := ProbabilityTheory.cond P A with hQ
  have hX0 : Measurable[ℱ ((0 : ℝ≥0) : ℝ)] (X 0) := hF.adapted 0
  have hX0' : Measurable[ℱ 0] X₀ := by
    have := hF.brownian.complete.measurable_of_ae_eq (0 : ℝ) (by have h := hX0; rw [NNReal.coe_zero] at h; exact h) hX₀ hinit
    exact this
  have hA0 : MeasurableSet[ℱ 0] A := hX0' hB
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
    exact indep_cond_sup_null (m1 := MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
      (m2 := ℱ s) (hincr s t).comap_le (ℱ.le _) (hF.brownian.indep_incr s t hst) (hAs s) hPB
  · intro s t hst
    refine ⟨(hincr s t).aemeasurable, ?_⟩
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply (hincr s t) hE]
    have := cond_value_of_indep (P := P) (m1 := MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
      (m2 := ℱ s) (hincr s t).comap_le (ℱ.le _) (hF.brownian.indep_incr s t hst) (hAs s) hPB
      (E := (fun ω => W' t ω - W' s ω) ⁻¹' E) ⟨E, hE, rfl⟩
    rw [this, ← Measure.map_apply (hincr s t) hE, (hF.brownian.gaussian_incr s t hst).map_eq]
  · exact ProbabilityTheory.cond_absolutelyContinuous.ae_le hF.coords
  · intro t
    exact (hF.adapted t).mono (hle _) le_rfl
  · intro i
    refine (hF.progressive i).mono ?_ le_rfl
    exact sup_le_sup_left (MeasurableSpace.comap_mono (hle i)) _

end Flow

end HRS.MC.CepH5Pf
