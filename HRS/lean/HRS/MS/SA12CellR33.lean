import HRS.MH.AdjointRdDefs

/-!
# S.A.12 R33: the exact binomial-jet identity `jetSq (m+1) = jetSq m + dissipSq m`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

/-- Reindexing of ordered derivative tuples of length `j+1` by (initial tuple, last coordinate). -/
theorem sa12_sum_snoc (d j : ℕ) (f : (Fin (j + 1) → Fin d) → ℝ) :
    ∑ idx : Fin (j + 1) → Fin d, f idx =
      ∑ idx : Fin j → Fin d, ∑ i : Fin d, f (Fin.snoc idx i : Fin (j + 1) → Fin d) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin d)).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem jetSq_succ (d m : ℕ) (w F : Euc d → ℝ) :
    jetSq (m+1) w F=jetSq m w F+dissipSq m w F := by
  set S : ℕ → ℝ := fun j => ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2 with hS
  have hSsucc : ∀ j, S (j + 1) = ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      ∫ x, (w x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 := fun j =>
    sa12_sum_snoc d j (fun idx => ∫ x, (w x * partialDeriv idx F x) ^ 2)
  have e1 : jetSq (m + 1) w F = ∑ j ∈ Finset.range (m + 2), (Nat.choose (m + 1) j : ℝ) * S j := rfl
  have e2 : jetSq m w F = ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * S j := rfl
  have e3 : dissipSq m w F = ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * S (j + 1) := by
    unfold dissipSq
    exact Finset.sum_congr rfl fun j _ => by rw [hSsucc j]
  rw [e1, e2, e3, Finset.sum_range_succ' _ (m + 1)]
  have e4 : ∀ j ∈ Finset.range (m + 1), (Nat.choose (m + 1) (j + 1) : ℝ) * S (j + 1) =
      (Nat.choose m j : ℝ) * S (j + 1) + (Nat.choose m (j + 1) : ℝ) * S (j + 1) := by
    intro j _
    rw [Nat.choose_succ_succ', Nat.cast_add]; ring
  rw [Finset.sum_congr rfl e4, Finset.sum_add_distrib]
  have e5 : ∑ j ∈ Finset.range (m + 1), (Nat.choose m (j + 1) : ℝ) * S (j + 1) +
      (Nat.choose (m + 1) 0 : ℝ) * S 0 = ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * S j := by
    rw [Finset.sum_range_succ' (fun j => (Nat.choose m j : ℝ) * S j) m,
      Finset.sum_range_succ (fun j => (Nat.choose m (j + 1) : ℝ) * S (j + 1)) m]
    simp [Nat.choose_succ_self]
  linarith

end HRS.MH.AdjointRd.Phase2SA12
