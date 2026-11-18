/-
# HRS.Equilibrium.Q84dAuxT — packet Q84d: the generator identity `β q 𝓛F = ∑_{ik} v_{ik}`
-/
import HRS.Equilibrium.Q84dAuxS

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_gen_identity {V : Torus d → ℝ} {β : ℝ} (hβ : 0 < β) {ψ : Torus d → Torus d → ℝ}
    (hsymm : IsSymmPair ψ) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (X : Config d N) (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) :
    β * qd d s V β X * particleGen d s V β (Fstat ψ) X =
      ∑ i, ∑ k, vik d s V β ψ i k X := by
  unfold particleGen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinner : inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) •
      ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i) =
      ∑ k, Bik d s V i k X * Aik d ψ i k X := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [q84d_configGrad_comp hsymm hsm X hX i k]
    simp [Bik, mul_comm]
  rw [hinner, q84d_configLap_eq hsymm hsm X hX i]
  unfold vik
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hβ0 : β ≠ 0 := hβ.ne'
  field_simp

end HRS.Q84d

end
