import HRS.Commutator.Torus.TEN2Aux8

/-!
# Torus energy layer (packet T-EN2), helper part 9: the counting inequality for the occupancy

Prefix `ten2_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s η : ℝ}

theorem ten2_occ_count (hη : 0 < η) (hη1 : η ≤ 1) (hN : 1 ≤ N) (X : Config d N) :
    ∑ j : Fin d → Fin (nCells η), occT η X j ^ 2 ≤
      1 / (N : ℝ) + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i' ∈ Finset.univ.erase i,
        (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) := by
  classical
  have hm := ten2_nCells_pos hη hη1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set m := nCells η with hmdef
  set ind : (Fin d → Fin m) → Fin N → ℝ := fun j i => if X i ∈ cellT m j then 1 else 0 with hind
  set W : Fin N → Fin N → ℝ := fun i i' =>
    if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then 1 else 0 with hW
  have hocc : ∀ j, occT η X j = (1 / (N : ℝ)) * ∑ i, ind j i := by
    intro j
    unfold occT
    congr 1
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hind]
    split_ifs <;> simp
  -- the pair bound
  have hpair : ∀ i i' : Fin N, ∑ j, ind j i * ind j i' ≤ W i i' := by
    intro i i'
    have hterm : ∀ j, ind j i * ind j i' = if (X i ∈ cellT m j ∧ X i' ∈ cellT m j) then 1 else 0 := by
      intro j
      simp only [hind]
      by_cases h1 : X i ∈ cellT m j <;> by_cases h2 : X i' ∈ cellT m j <;> simp [h1, h2]
    simp_rw [hterm]
    by_cases hnear : KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d
    · have hW1 : W i i' = 1 := by simp [hW, hnear]
      rw [hW1, Finset.sum_boole]
      have : (Finset.univ.filter fun j : Fin d → Fin m => X i ∈ cellT m j ∧ X i' ∈ cellT m j).card ≤ 1 := by
        refine Finset.card_le_one.2 fun j hj j' hj' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
        exact ten2_cell_unique (by omega) hj.1 hj'.1
      exact_mod_cast this
    · have hW0 : W i i' = 0 := by simp [hW, hnear]
      rw [hW0]
      refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
      have : ¬ (X i ∈ cellT m j ∧ X i' ∈ cellT m j) := fun h =>
        hnear (ten2_cell_tdist hη hη1 h.1 h.2)
      simp [this]
  have hdiag : ∀ i : Fin N, W i i ≤ 1 := by
    intro i; simp only [hW]; split_ifs <;> norm_num
  have hW0 : ∀ i i', 0 ≤ W i i' := by
    intro i i'; simp only [hW]; split_ifs <;> norm_num
  calc ∑ j, occT η X j ^ 2
      = (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i', ∑ j, ind j i * ind j i' := by
        have e1 : ∀ j : Fin d → Fin m, occT η X j ^ 2 =
            (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i', ind j i * ind j i' := by
          intro j
          rw [hocc j, mul_pow, sq (∑ i, ind j i), Finset.sum_mul_sum, one_div_pow]
        simp_rw [e1]
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i', W i i' := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hpair i i'
    _ ≤ 1 / (N : ℝ) + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i' ∈ Finset.univ.erase i, W i i' := by
        have h1 : ∀ i : Fin N, ∑ i', W i i' = W i i + ∑ i' ∈ Finset.univ.erase i, W i i' := fun i =>
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        simp_rw [h1, Finset.sum_add_distrib]
        have h2 : ∑ i : Fin N, W i i ≤ N := by
          calc ∑ i : Fin N, W i i ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hdiag i
            _ = N := by simp
        have h3 : (1 / (N : ℝ) ^ 2) * ∑ i : Fin N, W i i ≤ 1 / (N : ℝ) := by
          calc (1 / (N : ℝ) ^ 2) * ∑ i : Fin N, W i i ≤ (1 / (N : ℝ) ^ 2) * N :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = 1 / (N : ℝ) := by field_simp
        rw [mul_add]
        linarith
  
end HRS.Commutator.TorusNote
