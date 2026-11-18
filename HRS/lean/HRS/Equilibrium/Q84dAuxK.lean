/-
# HRS.Equilibrium.Q84dAuxK — packet Q84d: integrability of `F_N(ψ)` and `E_N(ψ)` (D2)
-/
import HRS.Equilibrium.Q84dAuxJ

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_exists_ne (hd : 1 ≤ d) : ∃ a c : Torus d, a ≠ c := by
  by_contra h
  push Not at h
  have h1 : (Set.univ : Set (Torus d)) = {0} := by
    ext x; simp [h x 0]
  have h2 := volume_singleton_torus hd (0 : Torus d)
  rw [← h1] at h2
  simp at h2

section Main

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_K_nonneg {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) : 0 ≤ K₁ := by
  obtain ⟨a, c, hac⟩ := q84d_exists_ne (d := d) (by omega)
  exact Q84a.q84a_K_nonneg hψ.size hac

/-- **D2, second conjunct**: `F_N(ψ)` is `P_{N,β}`-integrable. -/
theorem q84d_integrable_Fstat {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    Integrable (Fstat (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hK := q84d_K_nonneg hd hcrit hψ
  obtain ⟨C₁, hC₁0, hC₁⟩ := q84d_q_mul_w_le hd hcrit hV hβ hN
  have hψm : Measurable (fun p : Torus d × Torus d => ψ p.1 p.2) := hψ.measurable
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN
    (C := (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N * (N * (2 * K₁ * C₁)))) ?_ ?_
  · unfold Fstat
    exact (q84d_aesm_pairSum (N := N) hψm.aestronglyMeasurable).const_mul _
  · intro X hX
    set q := Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hXne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
    have hps := q84d_pairSum_bound q hq0 ψ X (M := 2 * K₁ * C₁) (by positivity) (fun i j hij => by
      have h1 := (hC₁ X i j hij).1
      have h2 := q84d_psi_le_w hs1 hψ.size hK (hXne i j hij)
      calc q * |ψ (X i) (X j)| ≤ q * (2 * K₁ * wEnv s (X i) (X j)) :=
            mul_le_mul_of_nonneg_left h2 hq0
        _ = 2 * K₁ * (q * wEnv s (X i) (X j)) := by ring
        _ ≤ 2 * K₁ * C₁ := mul_le_mul_of_nonneg_left h1 (by positivity))
    unfold Fstat
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_mul, abs_of_nonneg hN0]
    calc q * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * |pairSumOrdered ψ X|)
        = (N : ℝ) ^ (-(3 / 2 : ℝ)) * (q * |pairSumOrdered ψ X|) := by ring
      _ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N * (N * (2 * K₁ * C₁))) :=
          mul_le_mul_of_nonneg_left hps hN0

end Main

end HRS.Q84d

end
