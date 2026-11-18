/-
# HRS.Equilibrium.Q84eAuxA — packet Q84e: finite-sum combinatorics for the generator identity

Sums over ordered pairs / triples of distinct labels in `Fin N`: symmetry under relabelling and the
splitting `∑_i ∑_{j≠i} ∑_{k≠i} = (k = j) + (k distinct)`.
-/
import HRS.Equilibrium.PairCorrection

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

variable {N : ℕ}

/-- Ordered pairs of distinct labels as an indicator sum over all pairs. -/
theorem q84e_pair_ind (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j <;> simp [h, eq_comm]

/-- Swapping the two labels of an ordered pair sum. -/
theorem q84e_pair_swap (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f j i = ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  rw [q84e_pair_ind, q84e_pair_ind, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j <;> simp [h, eq_comm]

theorem q84e_sum_erase_ind (i : Fin N) (g : Fin N → ℝ) :
    ∑ j ∈ Finset.univ.erase i, g j = ∑ j, if j ≠ i then g j else 0 := by
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]

theorem q84e_sum_erase2_ind (i j : Fin N) (g : Fin N → ℝ) :
    ∑ k ∈ (Finset.univ.erase i).erase j, g k = ∑ k, if (k ≠ i ∧ k ≠ j) then g k else 0 := by
  have e : (Finset.univ.erase i).erase j = Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true]
    tauto
  rw [e, Finset.sum_filter]

/-- Triples of distinct labels as an indicator sum over all triples. -/
theorem q84e_triple_ind (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k =
      ∑ i, ∑ j, ∑ k, if (i ≠ j ∧ i ≠ k ∧ j ≠ k) then f i j k else 0 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [q84e_sum_erase_ind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · have hj : (j ≠ i) := fun h => hij h.symm
    simp only [hj, ne_eq, not_false_eq_true, ite_true]
    rw [q84e_sum_erase2_ind]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hij, fun h => h1 h.symm, fun h => h2 h.symm⟩
    · rintro ⟨_, h1, h2⟩; exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩

theorem q84e_triple_swap12 (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f j i k =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  rw [q84e_triple_ind, q84e_triple_ind, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : j = i <;> by_cases h2 : i = k <;> by_cases h3 : j = k <;> simp_all [eq_comm]

theorem q84e_triple_swap23 (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i k j =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  rw [q84e_triple_ind, q84e_triple_ind]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : i = k <;> by_cases h2 : i = j <;> by_cases h3 : j = k <;> simp_all [eq_comm]

theorem q84e_triple_cyc (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f j k i =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  exact (q84e_triple_swap12 (fun a b c => f b c a)).symm.trans (q84e_triple_swap23 f)

/-- A summand independent of the third label. -/
theorem q84e_triple_const (hN : 2 ≤ N) (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j =
      ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem (by simpa using Finset.ne_of_mem_erase hj),
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((N - 1 - 1 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]

/-- Splitting the third label `k ≠ i` of a triple sum into `k = j` and `k` distinct from both. -/
theorem q84e_triple_split (f : Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, f i j k =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j j +
        ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact (Finset.add_sum_erase _ (fun k => f i j k)
    hj).symm

/-- Sum over ordered triples of distinct labels. -/
def tS (f : Fin N → Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, f i j k

theorem tS_add (f g : Fin N → Fin N → Fin N → ℝ) :
    tS (fun i j k => f i j k + g i j k) = tS f + tS g := by
  unfold tS; simp only [Finset.sum_add_distrib]

theorem tS_sub (f g : Fin N → Fin N → Fin N → ℝ) :
    tS (fun i j k => f i j k - g i j k) = tS f - tS g := by
  unfold tS; simp only [Finset.sum_sub_distrib]

theorem tS_neg (f : Fin N → Fin N → Fin N → ℝ) :
    tS (fun i j k => -f i j k) = -tS f := by
  unfold tS; simp only [Finset.sum_neg_distrib]

theorem tS_const_mul (c : ℝ) (f : Fin N → Fin N → Fin N → ℝ) :
    tS (fun i j k => c * f i j k) = c * tS f := by
  unfold tS; simp only [← Finset.mul_sum]

theorem tS_swap12 (f : Fin N → Fin N → Fin N → ℝ) : tS (fun i j k => f j i k) = tS f :=
  q84e_triple_swap12 f

theorem tS_swap23 (f : Fin N → Fin N → Fin N → ℝ) : tS (fun i j k => f i k j) = tS f :=
  q84e_triple_swap23 f

theorem tS_cyc (f : Fin N → Fin N → Fin N → ℝ) : tS (fun i j k => f j k i) = tS f :=
  q84e_triple_cyc f

theorem tS_cyc' (f : Fin N → Fin N → Fin N → ℝ) : tS (fun i j k => f k i j) = tS f :=
  (tS_cyc (fun a b c => f c a b)).symm

theorem tS_rev (f : Fin N → Fin N → Fin N → ℝ) : tS (fun i j k => f k j i) = tS f :=
  (tS_swap12 (fun a b c => f c a b)).trans (tS_cyc' f)

theorem tS_pair (hN : 2 ≤ N) (g : Fin N → Fin N → ℝ) :
    tS (fun i j _ => g i j) = ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, g i j :=
  q84e_triple_const hN g

end HRS.Q84e

end
