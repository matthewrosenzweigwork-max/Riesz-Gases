import Mathlib

/-!
# SA16P, part 1: the Riesz representation of `(L^p)^*` (`1 < p < ∞`, σ-finite measure)

Mathlib has no description of the dual of `L^p`.  The frozen predicate `IsWmpWeaklyContinuous` quantifies over
EVERY `ℓ ∈ StrongDual (WmpSpace d m p)`, so the weak continuity of an `L^p` solution path needs it.

`sa16p_riesz`: for `p, q` Hölder conjugate and a bounded linear functional `ℓ` on `Lp ℝ p μ` there is a measurable
`g` with `‖g‖_q ≤ ‖ℓ‖` and `ℓ f = ∫ f g` for all `f` (the integrand is integrable by Hölder).

Proof: a positive weight `h ∈ L^p`; `A ↦ ℓ(1_A h)` is a signed measure absolutely continuous w.r.t. `μ`
(σ-additivity by dominated convergence in `L^p`), so it has a Radon-Nikodym density `G ∈ L^1`; `g = G / h`;
`ℓ(s h) = ∫ s G` for bounded measurable `s`; the norm bound by testing against the truncations of `|g|^{q-1} sign g`;
then extension to all `f` by dominated convergence.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Riesz
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

/-- a strictly positive measurable weight in `L^p` -/
lemma sa16p_weight {p : ℝ} (hp : 1 < p) :
    ∃ h : α → ℝ, Measurable h ∧ (∀ x, 0 < h x) ∧ MemLp h (ENNReal.ofReal p) μ := by
  obtain ⟨w, hw0, hwm, hwint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  have hp0 : 0 < p := by linarith
  refine ⟨fun x => ((w x : ℝ≥0) : ℝ) ^ (1 / p), ?_, fun x => ?_, ?_⟩
  · exact (measurable_coe_nnreal_real.comp hwm).pow_const _
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hw0 x) _
  · rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp; linarith) (by simp)]
    have : ∀ x, ‖((w x : ℝ≥0) : ℝ) ^ (1 / p)‖ₑ ^ (ENNReal.ofReal p).toReal = (w x : ℝ≥0∞) := by
      intro x
      rw [ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal (by positivity)]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← Real.rpow_mul (by positivity),
        one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      simp
    simp_rw [this]
    · exact lt_trans hwint ENNReal.one_lt_top
    · exact ((measurable_coe_nnreal_real.comp hwm).pow_const _).aestronglyMeasurable

end Riesz

section Ind
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ)

/-- `1_A h` as an element of `L^p` -/
def sa16p_ind (A : Set α) (hA : MeasurableSet A) : Lp ℝ (ENNReal.ofReal p) μ :=
  (hh.indicator hA).toLp (A.indicator h)

lemma sa16p_ind_coe (A : Set α) (hA : MeasurableSet A) :
    (sa16p_ind hh A hA : α → ℝ) =ᵐ[μ] A.indicator h :=
  MemLp.coeFn_toLp _

lemma sa16p_ind_add {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hAB : MeasurableSet (A ∪ B)) :
    sa16p_ind hh (A ∪ B) hAB = sa16p_ind hh A hA + sa16p_ind hh B hB := by
  apply Lp.ext
  filter_upwards [sa16p_ind_coe hh (A ∪ B) hAB, sa16p_ind_coe hh A hA, sa16p_ind_coe hh B hB,
    Lp.coeFn_add (sa16p_ind hh A hA) (sa16p_ind hh B hB)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, Set.indicator_union_of_disjoint hd]

lemma sa16p_ind_empty : sa16p_ind hh ∅ MeasurableSet.empty = 0 := by
  apply Lp.ext
  filter_upwards [sa16p_ind_coe hh ∅ MeasurableSet.empty, Lp.coeFn_zero ℝ (ENNReal.ofReal p) μ] with x h1 h2
  rw [h1, h2]
  simp

/-- the finite measure `‖h‖^p dμ` -/
def sa16p_mm (μ : Measure α) (h : α → ℝ) (p : ℝ) : Measure α :=
  μ.withDensity (fun x => ‖h x‖ₑ ^ p)

lemma sa16p_eLpNorm_ind_rpow (hh : MemLp h (ENNReal.ofReal p) μ) (hp : 1 < p) {S : Set α}
    (hS : MeasurableSet S) :
    eLpNorm (S.indicator h) (ENNReal.ofReal p) μ ^ p = sa16p_mm μ h p S := by
  have hp0 : 0 < p := by linarith
  have h1 : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) (by simp) (hh.aestronglyMeasurable.indicator hS), h1, sa16p_mm,
    withDensity_apply _ hS, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one,
    ← lintegral_indicator hS]
  congr 1
  funext x
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx, hp0]

lemma sa16p_mm_univ_lt_top (hh : MemLp h (ENNReal.ofReal p) μ) (hp : 1 < p) : sa16p_mm μ h p univ < ⊤ := by
  have hp0 : 0 < p := by linarith
  have := sa16p_eLpNorm_ind_rpow hh hp (MeasurableSet.univ)
  rw [Set.indicator_univ] at this
  rw [← this]
  exact ENNReal.rpow_lt_top_of_nonneg hp0.le hh.eLpNorm_ne_top

lemma sa16p_ind_congr {A A' : Set α} (hA : MeasurableSet A) (hA' : MeasurableSet A') (e : A = A') :
    sa16p_ind hh A hA = sa16p_ind hh A' hA' := by
  subst e; rfl

lemma sa16p_norm_ind_le (hp : 1 < p) {S : Set α} (hS : MeasurableSet S) {ε : ℝ} (hε : 0 < ε)
    (hm : sa16p_mm μ h p S < ENNReal.ofReal (ε ^ p)) : ‖sa16p_ind hh S hS‖ < ε := by
  have hp0 : 0 < p := by linarith
  have h1 := sa16p_eLpNorm_ind_rpow hh hp hS
  have hlt : eLpNorm (S.indicator h) (ENNReal.ofReal p) μ < ENNReal.ofReal ε := by
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : ENNReal.ofReal ε ^ p ≤ eLpNorm (S.indicator h) (ENNReal.ofReal p) μ ^ p :=
      ENNReal.rpow_le_rpow hcon hp0.le
    rw [h1, ENNReal.ofReal_rpow_of_nonneg hε.le hp0.le] at h2
    exact absurd hm (not_lt.2 h2)
  have hne : eLpNorm (S.indicator h) (ENNReal.ofReal p) μ ≠ ⊤ := (lt_trans hlt ENNReal.ofReal_lt_top).ne
  have : ‖sa16p_ind hh S hS‖ = (eLpNorm (S.indicator h) (ENNReal.ofReal p) μ).toReal := by
    rw [sa16p_ind, Lp.norm_toLp]
  rw [this]
  exact (ENNReal.toReal_lt_of_lt_ofReal hlt)

lemma sa16p_sum_ind {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f))
    (F : Finset ℕ) :
    ∑ i ∈ F, sa16p_ind hh (f i) (hf i) =
      sa16p_ind hh (⋃ i ∈ F, f i) (Finset.measurableSet_biUnion F (fun i _ => hf i)) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    rw [sa16p_ind_congr hh (Finset.measurableSet_biUnion ∅ (fun i _ => hf i)) MeasurableSet.empty
      (by simp), sa16p_ind_empty]
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, ih]
    have hU : (⋃ i ∈ insert a F, f i) = f a ∪ ⋃ i ∈ F, f i := by
      ext x; simp
    rw [sa16p_ind_congr hh (Finset.measurableSet_biUnion (insert a F) (fun i _ => hf i))
      ((hf a).union (Finset.measurableSet_biUnion F (fun i _ => hf i))) hU]
    rw [sa16p_ind_add hh (hf a) (Finset.measurableSet_biUnion F (fun i _ => hf i)) ?_]
    rw [Set.disjoint_iUnion₂_right]
    intro j hj
    exact hd (fun hja => ha (hja ▸ hj))

lemma sa16p_hasSum_ind (hp : 1 < p) {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => sa16p_ind hh (f i) (hf i)) (sa16p_ind hh (⋃ i, f i) (MeasurableSet.iUnion hf)) := by
  have hp0 : 0 < p := by linarith
  set B := ⋃ i, f i with hB
  have hBm : MeasurableSet B := MeasurableSet.iUnion hf
  -- summability of the masses
  have hsum : ∑' i, sa16p_mm μ h p (f i) = sa16p_mm μ h p B := (measure_iUnion hd hf).symm
  have hfin : ∑' i, sa16p_mm μ h p (f i) ≠ ⊤ := by
    rw [hsum]
    exact (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (sa16p_mm_univ_lt_top hh hp)).ne
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero (f := fun i => sa16p_mm μ h p (f i)) hfin
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ p) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨F₀, hF₀⟩ := (Filter.eventually_atTop.1 ((htail.eventually (gt_mem_nhds hpos))))
  refine ⟨F₀, fun F hF => ?_⟩
  have hlt := hF₀ F hF
  rw [sa16p_sum_ind hh hf hd F]
  set U := ⋃ i ∈ F, f i with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion F (fun i _ => hf i)
  have hUB : U ⊆ B := Set.iUnion₂_subset (fun i _ => Set.subset_iUnion f i)
  have hdiff : MeasurableSet (B \ U) := hBm.diff hUm
  have hsplit : sa16p_ind hh B hBm = sa16p_ind hh U hUm + sa16p_ind hh (B \ U) hdiff := by
    rw [← sa16p_ind_add hh hUm hdiff Set.disjoint_sdiff_right (hUm.union hdiff)]
    exact sa16p_ind_congr hh hBm _ (by rw [Set.union_sdiff_cancel hUB])
  have hmm : sa16p_mm μ h p (B \ U) = ∑' b : {x // x ∉ F}, sa16p_mm μ h p (f b) := by
    have : B \ U = ⋃ b : {x // x ∉ F}, f b := by
      ext x
      simp only [hB, hU, Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and, Subtype.exists]
      constructor
      · rintro ⟨⟨i, hi⟩, hx⟩
        exact ⟨i, fun hiF => hx i hiF hi, hi⟩
      · rintro ⟨i, hiF, hi⟩
        refine ⟨⟨i, hi⟩, fun j hj hxj => ?_⟩
        have hij : i ≠ j := fun e => hiF (by rw [e]; exact hj)
        exact Set.disjoint_left.1 (hd hij) hi hxj
    rw [this, measure_iUnion]
    · intro a b hab
      exact hd (fun e => hab (Subtype.ext e))
    · exact fun b => hf b
  rw [dist_eq_norm, hsplit, sub_add_cancel_left, norm_neg]
  exact sa16p_norm_ind_le hh hp hdiff hε (by rw [hmm]; exact hlt)

end Ind

end HRS.Whole.AppendixA.Phase2SA16P
