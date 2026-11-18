/-
# HRS.Equilibrium.Q84eAuxC — packet Q84e: pair and triple sums of `B_ψ`, `G_ψ` in scalar form
-/
import HRS.Equilibrium.Q84eAuxB

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- `∑_{i≠j} B_ψ(x_i,x_j) = 2 S_g - 4 S_F`. -/
theorem q84e_pairSum_Bpsi (hsd : s < d) (ρ : Torus d → ℝ) {ψ : Torus d → Torus d → ℝ}
    (hsymm : IsSymmPair ψ) (X : Config d N) :
    pairSumOrdered (Bpsi d s ρ ψ) X =
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X i) (X j)) -
        4 * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)) := by
  have hodd : ∀ a b : Torus d, periodicRieszGrad d s (b - a) = -periodicRieszGrad d s (a - b) := by
    intro a b
    have e : b - a = -(a - b) := by abel
    rw [e, HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]
  have hpt : ∀ i j : Fin N, Bpsi d s ρ ψ (X i) (X j) =
      inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X i) (X j)) -
      inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X j) (X i)) -
      2 * inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)) -
      2 * inner ℝ (forceField d s ρ (X j)) (gradFst ψ (X j) (X i)) := by
    intro i j
    unfold Bpsi Vpsi
    rw [Q84.q84_gradSnd_eq hsymm, inner_sub_right]
    ring
  unfold pairSumOrdered
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X j) (X i)) =
      -∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X i) (X j)) := by
    have := q84e_pair_swap (N := N) (fun i j =>
      inner ℝ (periodicRieszGrad d s (X j - X i)) (gradFst ψ (X i) (X j)))
    refine this.trans ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hodd, inner_neg_left]
  have h2 := q84e_pair_swap (N := N) (fun i j =>
    inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)))
  rw [h1, h2]
  ring

/-- The triple sum of `G_ψ` in scalar form. -/
theorem q84e_tripleSum_Gpsi (hN : 2 ≤ N) (ρ : Torus d → ℝ) {ψ : Torus d → Torus d → ℝ}
    (hsymm : IsSymmPair ψ) (X : Config d N) :
    tripleSum (Gpsi d s ρ ψ) X =
      -2 * tS (fun i j k : Fin N =>
          inner ℝ (periodicRieszGrad d s (X i - X k)) (gradFst ψ (X i) (X j))) +
        2 * ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)) -
        ((N : ℝ) - 2) * pairSumOrdered (Jpair d s ρ ψ) X := by
  -- opaque names for the building blocks
  obtain ⟨U, hU⟩ : ∃ U : Fin N → Fin N → Fin N → ℝ, U = fun a b c =>
      inner ℝ (periodicRieszGrad d s (X a - X c)) (gradFst ψ (X a) (X b)) -
        inner ℝ (forceField d s ρ (X a)) (gradFst ψ (X a) (X b)) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Fin N → Fin N → ℝ, J = fun a b => Jpair d s ρ ψ (X a) (X b) := ⟨_, rfl⟩
  have key : ∀ i j k : Fin N, Gpsi d s ρ ψ (X i) (X j) (X k) =
      ((-1 / 3) * U i j k + (-1 / 3) * U j i k + (-1 / 3) * U i k j + (-1 / 3) * U k i j +
        (-1 / 3) * U j k i + (-1 / 3) * U k j i) +
      ((-1 / 3) * J i j + (-1 / 3) * J i k + (-1 / 3) * J j k) := by
    intro i j k
    simp only [hU, hJ, Gpsi, Tpsi, centeredForce, Q84.q84_gradSnd_eq hsymm, inner_sub_left]
    ring
  have h1 : tripleSum (Gpsi d s ρ ψ) X = tS (fun i j k : Fin N =>
      ((-1 / 3) * U i j k + (-1 / 3) * U j i k + (-1 / 3) * U i k j + (-1 / 3) * U k i j +
        (-1 / 3) * U j k i + (-1 / 3) * U k j i) +
      ((-1 / 3) * J i j + (-1 / 3) * J i k + (-1 / 3) * J j k)) := by
    unfold tripleSum tS
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    exact key i j k
  rw [h1]
  have hJ2 : tS (fun i j _ : Fin N => J i j) = ((N : ℝ) - 2) * pairSumOrdered (Jpair d s ρ ψ) X := by
    rw [tS_pair hN, hJ]; rfl
  simp only [tS_add, tS_const_mul]
  rw [tS_swap12 U, tS_swap23 U, tS_cyc' U, tS_cyc U, tS_rev U]
  rw [tS_swap23 (fun a b _ => J a b), tS_cyc (fun a b _ => J a b)]
  have hUs : tS U = tS (fun i j k : Fin N =>
      inner ℝ (periodicRieszGrad d s (X i - X k)) (gradFst ψ (X i) (X j))) -
      ((N : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)) := by
    rw [hU, tS_sub, tS_pair hN (fun i j => inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)))]
  rw [hUs]
  linear_combination (-1) * hJ2


end HRS.Q84e

end
