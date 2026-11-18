/-
# HRS.Equilibrium.Q84eAuxB — packet Q84e: the generator on `F_N(ψ)` in vector form
-/
import HRS.Equilibrium.Q84dStationary
import HRS.Equilibrium.Q84eAuxA

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- `∇_i F_N(ψ)` as a vector. -/
theorem q84e_configGrad_vec {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    configGrad (Fstat ψ) X i =
      (2 * (N : ℝ) ^ (-(3 / 2 : ℝ))) • ∑ j ∈ Finset.univ.erase i, gradFst ψ (X i) (X j) := by
  ext k
  rw [q84d_configGrad_comp hsymm hsm X hX i k]
  unfold Aik
  simp only [PiLp.smul_apply, smul_eq_mul]
  congr 1
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold gradFst
  rw [q84d_grad_comp hsm (hX i j (Finset.ne_of_mem_erase hj).symm) k]

/-- `Δ_i F_N(ψ)`. -/
theorem q84e_configLap_vec {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    configLap (Fstat ψ) X i =
      (2 * (N : ℝ) ^ (-(3 / 2 : ℝ))) *
        ∑ j ∈ Finset.univ.erase i, Torus.laplacian (fun z => ψ z (X j)) (X i) := by
  rw [q84d_configLap_eq hsymm hsm X hX i]
  unfold Cik
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [q84d_lap_comp hsm (hX i j (Finset.ne_of_mem_erase hj).symm)]

theorem q84e_inner_aux {ι κ : Type*} (S : Finset ι) (S' : Finset κ) (u : Euc d) (G : ι → Euc d)
    (A : κ → Euc d) (c m : ℝ) :
    inner ℝ (u + m • ∑ k ∈ S, G k) (c • ∑ j ∈ S', A j) =
      c * ∑ j ∈ S', inner ℝ u (A j) + c * m * ∑ j ∈ S', ∑ k ∈ S, inner ℝ (G k) (A j) := by
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  rw [← Finset.mul_sum]
  ring

/-- The generator on `F_N(ψ)` in terms of five scalar double/triple sums. -/
theorem q84e_particleGen_eq (V : Torus d → ℝ) (β : ℝ) {ψ : Torus d → Torus d → ℝ}
    (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) :
    particleGen d s V β (Fstat ψ) X =
      2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (β⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
          Torus.laplacian (fun z => ψ z (X j)) (X i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Torus.grad V (X i)) (gradFst ψ (X i) (X j))) -
      2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / (N : ℝ)) *
        (∑ i, ∑ j ∈ Finset.univ.erase i,
            inner ℝ (periodicRieszGrad d s (X i - X j)) (gradFst ψ (X i) (X j)) +
          ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
            inner ℝ (periodicRieszGrad d s (X i - X k)) (gradFst ψ (X i) (X j))) := by
  unfold particleGen
  have h1 : ∀ i : Fin N, β⁻¹ * configLap (Fstat ψ) X i -
      inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i) =
      2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (β⁻¹ * ∑ j ∈ Finset.univ.erase i,
          Torus.laplacian (fun z => ψ z (X j)) (X i) -
        ∑ j ∈ Finset.univ.erase i, inner ℝ (Torus.grad V (X i)) (gradFst ψ (X i) (X j))) -
      2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
            inner ℝ (periodicRieszGrad d s (X i - X k)) (gradFst ψ (X i) (X j)) := by
    intro i
    rw [q84e_configLap_vec hsymm hsm X hX i, q84e_configGrad_vec hsymm hsm X hX i,
      q84e_inner_aux]
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [q84e_triple_split (fun i j k => inner ℝ (periodicRieszGrad d s (X i - X k))
    (gradFst ψ (X i) (X j)))]

end HRS.Q84e

end
