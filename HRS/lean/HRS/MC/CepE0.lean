import HRS.Torus.Basic

/-!
# Packet CEPE0: measurable sorting of the initial configuration (`cep_E0_sort`)

`HRS.MC.CepE0.cep_E0_sort_proof` has the statement of `HRS.MC.Cepa.cep_E0_sort`.  The sorting permutation is
`Tuple.sort` of the vector of representatives in `[0,1)`; its level sets are measurable by the
characterisation `Tuple.eq_sort_iff`.  The vocabulary `cep_StrictlyOrdered` is re-stated here (identical body)
so that this module does not import the (sorried) spec file; the tie file checks the identity.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE0

open HRS

theorem cepe0_measurable_repVec (N : ℕ) :
    Measurable (fun (x : Config 1 N) (i : Fin N) => Torus.rep (x i) 0) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h : Measurable (fun (x : Torus 1) => ((AddCircle.equivIco (1 : ℝ) 0 (x 0) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply 0))
  exact h.comp (measurable_pi_apply i)

theorem cepe0_measurableSet_sort (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {v : Fin N → ℝ | Tuple.sort v = σ} := by
  have : {v : Fin N → ℝ | Tuple.sort v = σ} =
      (⋂ i : Fin N, ⋂ j : Fin N, {v : Fin N → ℝ | i ≤ j → v (σ i) ≤ v (σ j)}) ∩
        ⋂ i : Fin N, ⋂ j : Fin N, {v : Fin N → ℝ | i < j → v (σ i) = v (σ j) → σ i < σ j} := by
    ext v
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    simp only [Monotone, Function.comp]
  rw [this]
  have hm : ∀ i : Fin N, Measurable (fun v : Fin N → ℝ => v (σ i)) := fun i => measurable_pi_apply _
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases h : i ≤ j
    · simp only [h, forall_const]
      exact measurableSet_le (hm i) (hm j)
    · simp [h]
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases h : i < j
    · simp only [h, forall_const]
      by_cases h2 : σ i < σ j
      · simp [h2]
      · simp only [h2, imp_false]
        exact (measurableSet_eq_fun (hm i) (hm j)).compl
    · simp [h]

theorem cepe0_rep_injective (a b : Torus 1) (h : Torus.rep a 0 = Torus.rep b 0) : a = b := by
  have h0 : a 0 = b 0 := by
    have := Subtype.ext h
    exact (AddCircle.equivIco (1 : ℝ) 0).injective this
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact h0

/-- Strict cyclic order of a lift (copy of `cep_StrictlyOrdered`). -/
def cepe0_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

theorem cep_E0_sort_proof (N : ℕ) : ∃ π : Config 1 N → Equiv.Perm (Fin N),
    (∀ σ, MeasurableSet {x | π x = σ}) ∧
      ∀ x : Config 1 N, x ∉ collisionSet 1 N → cepe0_StrictlyOrdered (π x) (fun i => Torus.rep (x i)) := by
  refine ⟨fun x => Tuple.sort (fun i => Torus.rep (x i) 0), fun σ => ?_, fun x hx => ?_⟩
  · exact (cepe0_measurableSet_sort N σ).preimage (cepe0_measurable_repVec N)
  · set v : Fin N → ℝ := fun i => Torus.rep (x i) 0 with hv
    have hinj : Function.Injective v := by
      intro i j hij
      by_contra hne
      exact hx ⟨i, j, hne, cepe0_rep_injective _ _ hij⟩
    have hmono : Monotone (v ∘ Tuple.sort v) := Tuple.monotone_sort v
    refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
    · have h1 : v (Tuple.sort v k) ≤ v (Tuple.sort v k') := hmono hkk'.le
      have h2 : v (Tuple.sort v k) ≠ v (Tuple.sort v k') := fun h =>
        (ne_of_lt hkk') ((Tuple.sort v).injective (hinj h))
      exact lt_of_le_of_ne h1 h2
    · have h1 : Torus.rep (x (Tuple.sort v k')) 0 < 1 := by
        have := ((AddCircle.equivIco (1 : ℝ) 0 (x (Tuple.sort v k') 0)).2).2
        simpa [Torus.rep] using this
      have h0 : 0 ≤ Torus.rep (x (Tuple.sort v k)) 0 := by
        have := ((AddCircle.equivIco (1 : ℝ) 0 (x (Tuple.sort v k) 0)).2).1
        simpa [Torus.rep] using this
      show Torus.rep (x (Tuple.sort v k')) 0 < Torus.rep (x (Tuple.sort v k)) 0 + 1
      linarith

end HRS.MC.CepE0
