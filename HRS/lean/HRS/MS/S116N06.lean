import HRS.MS.S116N05
import HRS.MS.S113EndAux6

/-!
# S11.6 packet N06 (`R26-T8B.N06`): the iid Radon-Nikodym power moment with the negative auxiliary temperature

Prefix `s116_`, namespace `HRS.MS.S116`.  `p₁ = 1 + a_*/β` with `a_*` from `s116_log_normalizers` (N05, positive endpoint `β₊ = β`): for `1 < p < p₁` the auxiliary temperature `-(p-1)β`
lies in `[-a_*, β]`, so the native exact formula `s113x_initial_moment_zero` applies with the uniform logarithmic bound of N05.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_iid_power {d : ℕ} (hd : 2 ≤ d) (M L Cg cg β : ℝ)
    (hcg : 0 < cg) (hβ : 0 < β) :
    ∃ p₁ : ℝ, 1 < p₁ ∧ ∀ p : ℝ, 1 < p → p < p₁ →
      ∃ B : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d 0 M L ρ → HasR2GaussianUpper Cg cg ρ →
      ∀ N : ℕ, 2 ≤ N →
        (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) ≪
          HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ) ∧
        (∫⁻ X, ENNReal.ofReal ((((Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ).rnDeriv
          (HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))) X).toReal ^ p)
          ∂(HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ))) ≤ ENNReal.ofReal B := by
  obtain ⟨astar, B0, hastar, hB0, hN5⟩ := s116_log_normalizers hd M L Cg cg β hcg hβ
  have hd0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    linarith
  refine ⟨1 + astar / β, by have := div_pos hastar hβ; linarith, fun p hp hpp => ?_⟩
  obtain ⟨K, hK⟩ := HRS.MS.S113BD.s113x_initial_moment_zero hd (s := 0) le_rfl hd0 M L (β := β) (p₀ := p)
    (K₀ := B0) hβ hp
  refine ⟨K, fun ρ hρ hG N hN => hK ρ hρ N hN ?_⟩
  have hlt : (p - 1) * β ≤ astar := by
    have h1 : p - 1 < astar / β := by linarith
    have := (lt_div_iff₀ hβ).1 h1
    linarith
  refine hN5 ρ hρ hG N hN (p * 0 - (p - 1) * β) ⟨?_, ?_⟩
  · linarith
  · have : 0 ≤ (p - 1) * β := mul_nonneg (by linarith) hβ.le
    linarith

end HRS.MS.S116

end
