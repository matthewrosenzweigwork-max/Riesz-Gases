import HRS.MS.R26T8AR05a
import HRS.MS.MfeConfAux170

/-!
# S8.2 local Newton layer, packet T8A.R05 (part b): the ordered pair sum of an even kernel is twice the sum over `i < j`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_r05_pairSum_two {d N : ℕ} {k : Euc d → ℝ} (hev : ∀ x, k (-x) = k x) (Z : HRS.Whole.EucConfig d N) :
    HRS.MS.Phase2S82.pairSum (fun x y => k (x - y)) Z = 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) := by
  unfold HRS.MS.Phase2S82.pairSum
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, k (Z i - Z j) =
      ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), k (Z i - Z j) := by
    intro i
    have : Finset.univ.erase i = Finset.univ.filter (fun j => i < j) ∪ Finset.univ.filter (fun j => j < i) := by
      ext j; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inr ⟨trivial, h'⟩
        · exact Or.inl ⟨trivial, h'⟩
      · rintro (h | h)
        · exact h.2.ne'
        · exact h.2.ne
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_filter]
    intro j _ h1 h2; exact lt_asymm h1 h2
  simp only [h1, Finset.sum_add_distrib]
  have h2 : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j < i), k (Z i - Z j) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), k (Z i - Z j) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · simp only [h, if_true]
      rw [← hev, neg_sub]
    · simp [h]
  rw [h2]; ring

end HRS.MS.R26T8A
