import HRS.MC.CepN6Aux7
import HRS.MC.CepN3

/-!
# Packet CEPN6 (aux 8): initial separation from N3, N4-conditions from the closed good set, the sorting
permutation
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {N : ℕ}

theorem n6_hinit_of_N3 (hN : 2 ≤ N) {σ : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} {r : ℝ}
    (hiso : cep_PairIsolated hN σ y r)
    (hsep : ∀ k l : Fin N, k ≠ l → k ≠ σ (cep_i0 hN) → k ≠ σ (cep_i1 hN) →
      l ≠ σ (cep_i0 hN) → l ≠ σ (cep_i1 hN) → ∀ m : ℤ, r ≤ |y k 0 - y l 0 - m|) :
    ∀ k l, n6_rel (σ (cep_i0 hN)) (σ (cep_i1 hN)) k l → r ≤ n6_dc (y k 0 - y l 0) := by
  intro k l ⟨hkl, hnot⟩
  refine n6_le_dc fun m => ?_
  by_cases hk : k = σ (cep_i0 hN) ∨ k = σ (cep_i1 hN)
  · have hl0 : l ≠ σ (cep_i0 hN) := fun h => hnot ⟨hk, Or.inl h⟩
    have hl1 : l ≠ σ (cep_i1 hN) := fun h => hnot ⟨hk, Or.inr h⟩
    have key : |y k 0 - y l 0 - m| = |y l 0 - y k 0 - ((-m : ℤ) : ℝ)| := by
      rw [← abs_neg]; congr 1; push_cast; ring
    rw [key]
    rcases hk with rfl | rfl
    · exact (hiso l hl0 hl1 (-m)).1
    · exact (hiso l hl0 hl1 (-m)).2
  · push_neg at hk
    by_cases hl : l = σ (cep_i0 hN) ∨ l = σ (cep_i1 hN)
    · rcases hl with rfl | rfl
      · exact (hiso k hk.1 hk.2 m).1
      · exact (hiso k hk.1 hk.2 m).2
    · push_neg at hl
      exact hsep k l hkl hk.1 hk.2 hl.1 hl.2 m

/-- On the closed good set the hypotheses of the gap dynamics (N4) hold. -/
theorem n6_condN4 (hN : 2 ≤ N) (σ : Equiv.Perm (Fin N)) {y : ℝ → Fin N → Euc 1} {r2 s t : ℝ}
    (hK : ∀ u ∈ Set.Icc s t, y u ∈ n6_Kc (σ (cep_i0 hN)) (σ (cep_i1 hN)) r2 (1 / 8))
    (hord : ∀ u ∈ Set.Icc s t, cep_StrictlyOrdered σ (y u)) :
    ∀ u ∈ Set.Icc s t, cep_StrictlyOrdered σ (y u) ∧ cep_PairIsolated hN σ (y u) r2 ∧
      0 < y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 ∧
      y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 < 1 / 4 := by
  intro u hu
  set p0 := σ (cep_i0 hN) with hp0
  set p1 := σ (cep_i1 hN) with hp1
  have huK := hK u hu
  have hlt01 : cep_i0 hN < cep_i1 hN := by
    show (⟨0, _⟩ : Fin N) < ⟨1, _⟩
    exact Fin.mk_lt_mk.2 one_pos
  have hgap : 0 < y u p1 0 - y u p0 0 := by
    have := (hord u hu).1 _ _ hlt01
    linarith
  refine ⟨hord u hu, ?_, hgap, ?_⟩
  · intro k hk0 hk1 m
    have r0 : n6_rel p0 p1 k p0 := ⟨hk0, fun h => by
      rcases h with ⟨h | h, _⟩
      · exact hk0 h
      · exact hk1 h⟩
    have r1 : n6_rel p0 p1 k p1 := ⟨hk1, fun h => by
      rcases h with ⟨h | h, _⟩
      · exact hk0 h
      · exact hk1 h⟩
    exact ⟨le_trans (huK.2 k p0 r0) (n6_dc_le _ m), le_trans (huK.2 k p1 r1) (n6_dc_le _ m)⟩
  · have := huK.1
    linarith

/-! ### The sorting permutation -/

theorem n6_coord_ne {y : Fin N → Euc 1} (hy : y ∈ liftedFree 1 N) {a b : Fin N} (hab : a ≠ b) :
    y a 0 ≠ y b 0 := fun h => cepn4_ne_int hy hab 0 (by simpa using sub_eq_zero.2 h)

/-- The permutation sorting the coordinates. -/
def n6_pi {Ω : Type*} (Y₀ : Ω → Fin N → Euc 1) (ω : Ω) : Equiv.Perm (Fin N) :=
  Tuple.sort (fun k => Y₀ ω k 0)

theorem n6_pi_meas {Ω : Type*} {m : MeasurableSpace Ω} {Y₀ : Ω → Fin N → Euc 1}
    (hm : Measurable Y₀) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {ω | n6_pi Y₀ ω = σ} := by
  have hf : ∀ k : Fin N, Measurable fun ω => Y₀ ω k 0 := fun k =>
    (n6_coord_cont k).measurable.comp hm
  have : {ω | n6_pi Y₀ ω = σ} =
      {ω | Monotone ((fun k => Y₀ ω k 0) ∘ σ) ∧
        ∀ i j : Fin N, i < j → Y₀ ω (σ i) 0 = Y₀ ω (σ j) 0 → σ i < σ j} := by
    ext ω
    simp only [Set.mem_setOf_eq, n6_pi]
    rw [eq_comm]
    exact Tuple.eq_sort_iff
  rw [this]
  have e : {ω | Monotone ((fun k => Y₀ ω k 0) ∘ σ) ∧
        ∀ i j : Fin N, i < j → Y₀ ω (σ i) 0 = Y₀ ω (σ j) 0 → σ i < σ j} =
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≤ j → Y₀ ω (σ i) 0 ≤ Y₀ ω (σ j) 0}) ∩
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i < j → Y₀ ω (σ i) 0 = Y₀ ω (σ j) 0 → σ i < σ j}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Monotone, Function.comp]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases h : i ≤ j
    · simp only [h, true_imp_iff]
      exact measurableSet_le (hf _) (hf _)
    · simp [h]
  · by_cases h : i < j
    · simp only [h, true_imp_iff]
      by_cases h2 : σ i < σ j
      · simp [h2]
      · simp only [h2, imp_false]
        exact (measurableSet_eq_fun (hf _) (hf _)).compl
    · simp [h]

theorem n6_pi_strict {Ω : Type*} {Y₀ : Ω → Fin N → Euc 1} {ω : Ω}
    (hfree : Y₀ ω ∈ liftedFree 1 N) (hrng : ∀ i, Y₀ ω i 0 ∈ Set.Ico (0 : ℝ) 1) :
    cep_StrictlyOrdered (n6_pi Y₀ ω) (Y₀ ω) := by
  unfold n6_pi
  set π := Tuple.sort (fun k => Y₀ ω k 0) with hπ
  have hmono : Monotone ((fun k => Y₀ ω k 0) ∘ π) := Tuple.monotone_sort _
  refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
  · refine lt_of_le_of_ne (hmono hkk'.le) fun h => ?_
    exact n6_coord_ne hfree (fun e => hkk'.ne (π.injective e)) h
  · have h1 := (hrng (π k')).2
    have h2 := (hrng (π k)).1
    linarith

end HRS.MC.CepN6
