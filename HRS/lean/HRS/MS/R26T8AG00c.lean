import HRS.MS.R26T8AG00b

/-!
# S8.2 observed-time layer, packet T8A.G00 (helper c): symmetric pair sums

For a symmetric pair function `F`, the sum over ordered pairs `i ≠ j` is twice the sum over `i < j`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_g00c_sum_erase {α : Type*} {N : ℕ} (F : α → α → ℝ) (hF : ∀ x y, F x y = F y x)
    (X : Fin N → α) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, F (X i) (X j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), F (X i) (X j) := by
  have e1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, F (X i) (X j) =
      ∑ j, if i ≠ j then F (X i) (X j) else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [Finset.mem_erase, ne_comm]
  have e2 : ∀ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), F (X i) (X j) =
      ∑ j, if i < j then F (X i) (X j) else 0 := by
    intro i
    exact Finset.sum_filter _ _
  simp only [e1, e2]
  have hsplit : ∀ i j : Fin N, (if i ≠ j then F (X i) (X j) else 0) =
      (if i < j then F (X i) (X j) else 0) + (if j < i then F (X i) (X j) else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  simp only [hsplit, Finset.sum_add_distrib]
  have hswap : ∑ i : Fin N, ∑ j : Fin N, (if j < i then F (X i) (X j) else 0) =
      ∑ i : Fin N, ∑ j : Fin N, (if i < j then F (X i) (X j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hF]
  rw [hswap]
  ring

end HRS.MS.R26T8A

end
