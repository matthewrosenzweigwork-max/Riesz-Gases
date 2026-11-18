import Mathlib

/-!
# S8.2 A02 (S82V), part 2: finite bookkeeping for sums over distinct indices
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HRS.MS.S82V

/-- The sum over ordered distinct triples. -/
def s82v_sum3 {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, u i j k

lemma s82v_sum_erase_ind {N : ℕ} (i : Fin N) (f : Fin N → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j, if j ≠ i then f j else 0 := by
  rw [← Finset.sum_filter, Finset.filter_ne' ]

lemma s82v_sum3_ind {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 u = ∑ i, ∑ j, ∑ k, if (j ≠ i ∧ k ≠ i ∧ k ≠ j) then u i j k else 0 := by
  unfold s82v_sum3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s82v_sum_erase_ind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ≠ i
  · simp only [hj, ite_true, ne_eq, not_false_eq_true, true_and]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k; simp [Finset.mem_erase]; tauto
  · simp [hj]

lemma s82v_sum3_swap23 {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => u i k j) = s82v_sum3 u := by
  rw [s82v_sum3_ind, s82v_sum3_ind]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (k ≠ i ∧ j ≠ i ∧ j ≠ k)
  · have h' : (j ≠ i ∧ k ≠ i ∧ k ≠ j) := ⟨h.2.1, h.1, fun e => h.2.2 e.symm⟩
    simp [h, h']
  · have h' : ¬ (j ≠ i ∧ k ≠ i ∧ k ≠ j) := fun h2 => h ⟨h2.2.1, h2.1, fun e => h2.2.2 e.symm⟩
    simp [h, h']

lemma s82v_sum3_swap12 {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => u j i k) = s82v_sum3 u := by
  rw [s82v_sum3_ind, s82v_sum3_ind]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (i ≠ j ∧ k ≠ j ∧ k ≠ i)
  · have h' : (j ≠ i ∧ k ≠ i ∧ k ≠ j) := ⟨fun e => h.1 e.symm, h.2.2, h.2.1⟩
    simp [h, h']
  · have h' : ¬ (j ≠ i ∧ k ≠ i ∧ k ≠ j) := fun h2 => h ⟨fun e => h2.1 e.symm, h2.2.2, h2.2.1⟩
    simp [h, h']

lemma s82v_sum3_cyc {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => u j k i) = s82v_sum3 u := by
  rw [← s82v_sum3_swap23 (fun i j k => u i j k)]
  rw [← s82v_sum3_swap12 (fun i j k => u i k j)]

lemma s82v_sum3_add {N : ℕ} (u v : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => u i j k + v i j k) = s82v_sum3 u + s82v_sum3 v := by
  unfold s82v_sum3
  simp only [Finset.sum_add_distrib]

lemma s82v_sum3_sub {N : ℕ} (u v : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => u i j k - v i j k) = s82v_sum3 u - s82v_sum3 v := by
  unfold s82v_sum3
  simp only [Finset.sum_sub_distrib]

lemma s82v_sum3_neg {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j k => -u i j k) = -s82v_sum3 u := by
  unfold s82v_sum3
  simp only [Finset.sum_neg_distrib]

lemma s82v_sum3_div {N : ℕ} (u : Fin N → Fin N → Fin N → ℝ) (c : ℝ) :
    s82v_sum3 (fun i j k => u i j k / c) = s82v_sum3 u / c := by
  unfold s82v_sum3
  simp only [Finset.sum_div]

lemma s82v_sum3_pair {N : ℕ} (v : Fin N → Fin N → ℝ) :
    s82v_sum3 (fun i j _ => v i j) = ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, v i j := by
  unfold s82v_sum3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  have hc : ((Finset.univ.erase i).erase j).card = N - 2 := by
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp; omega
  rw [hc]
  have hN : 2 ≤ N := by
    have h1 : i ≠ j := fun e => hji e.symm
    have := Fintype.card_le_of_injective (fun b : Fin 2 => if b = 0 then i else j)
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
    simpa using this
  rw [Nat.cast_sub hN]; push_cast; ring

lemma s82v_pairsum_swap {N : ℕ} (v : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, v i j = ∑ i, ∑ j ∈ Finset.univ.erase i, v j i := by
  refine Finset.sum_comm' ?_
  intro i j
  simp [Finset.mem_erase]
  tauto

end HRS.MS.S82V

end
