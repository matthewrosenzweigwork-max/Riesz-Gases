/-
# HRS.Equilibrium.Q84eAuxD — packet Q84e: the lifted generator identity (source lines 4943-4952)

For `X` off collisions,
`𝓛F_N(ψ)(X) = N^{-3/2} ∑_{i≠j} [B(ψ(·,x_j))(x_i) + B(ψ(·,x_i))(x_j) + 𝒥ψ(x_i,x_j)] + E_N(ψ)(X)`,
a purely algebraic identity (symmetry of `ψ`, oddness of `∇g`, the finite-particle corrections
`(N-2)` of the triple sums).
-/
import HRS.Equilibrium.Q84eAuxC

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84e_gen_alg (hN : 2 ≤ N) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) :
    particleGen d s V β (Fstat ψ) X =
      (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered (fun x y =>
        Bop d s V β ρ (fun z => ψ z y) x + Bop d s V β ρ (fun z => ψ z x) y + Jpair d s ρ ψ x y) X +
      errStat d s ρ ψ X := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [q84e_particleGen_eq V β hsymm hsm X hX]
  -- the `B`-part
  have hB : ∑ i, ∑ j ∈ Finset.univ.erase i, Bop d s V β ρ (fun z => ψ z (X j)) (X i) =
      β⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian (fun z => ψ z (X j)) (X i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Torus.grad V (X i)) (gradFst ψ (X i) (X j)) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j)) := by
    simp only [Bop, inner_add_left, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold gradFst
    ring
  have hBswap := q84e_pair_swap (N := N) (fun i j => Bop d s V β ρ (fun z => ψ z (X j)) (X i))
  have hps : pairSumOrdered (fun x y =>
        Bop d s V β ρ (fun z => ψ z y) x + Bop d s V β ρ (fun z => ψ z x) y + Jpair d s ρ ψ x y) X =
      2 * (β⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.laplacian (fun z => ψ z (X j)) (X i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Torus.grad V (X i)) (gradFst ψ (X i) (X j)) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (forceField d s ρ (X i)) (gradFst ψ (X i) (X j))) +
      pairSumOrdered (Jpair d s ρ ψ) X := by
    unfold pairSumOrdered
    simp only [Finset.sum_add_distrib]
    rw [hBswap, hB]
    ring
  rw [hps]
  have hT := q84e_tripleSum_Gpsi hN ρ hsymm X (s := s)
  have hBp := q84e_pairSum_Bpsi hsd ρ hsymm X
  unfold errStat Fstat
  rw [hT, hBp]
  unfold tS
  have e52 : (N : ℝ) ^ (-(5 / 2 : ℝ)) = (N : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / (N : ℝ)) := by
    rw [show (-(5 / 2 : ℝ)) = -(3 / 2) + (-1) by norm_num, Real.rpow_add hNp, Real.rpow_neg_one]
    ring
  rw [e52]
  field_simp
  ring

end HRS.Q84e

end
