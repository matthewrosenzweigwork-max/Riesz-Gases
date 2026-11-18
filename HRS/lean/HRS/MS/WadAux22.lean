import HRS.MS.WadAux21
import HRS.MS.MovThermAux2

/-!
# S8.3, packet D4 (part 3): the first-order remainder `𝓑` is controlled by the weighted `C^{1,1/2}` norm

For a density `ρ` with `|ρ|, ‖Dρ‖ ≤ C e^{-c‖x‖²}` (`s84_GaussReg`; the thermal density, `s84_thermal_gaussReg`):
`s84_B_bound`: if `‖Dh(y)‖ ≤ V⟨y⟩^M` and `‖Dh(x') - Dh(x)‖ ≤ H‖x'-x‖^{1/2}⟨x⟩^M` (`‖x'-x‖ ≤ 1/4`) then
`|𝓑h(x)| ≤ C_B (V+H) ⟨x⟩^M`, where
`𝓑h = ⟨M(∇g*ρ), ∇h⟩ - Σ_j (∇g * (ρ (Mᵀ∇h)_j))_j` (`s84_Bop`, `M = -1`, `g = |x|^{-d/2}`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Differentiable density with Gaussian bounds on itself and its derivative. -/
def s84_GaussReg (ρ : Euc d → ℝ) : Prop :=
  Differentiable ℝ ρ ∧ ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ x : Euc d,
    |ρ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2) ∧ ‖fderiv ℝ ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)

theorem s84_thermal_gaussReg (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (h : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) : s84_GaussReg ρ := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hsm, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd ha hβ h
  obtain ⟨C₀, c₀, hc₀, h₀⟩ := hg 0
  obtain ⟨C₁, c₁, hc₁, h₁⟩ := hg 1
  have hdiff : Differentiable ℝ ρ := hsm.differentiable (by simp)
  refine ⟨hdiff, max C₀ C₁, min c₀ c₁, ?_, lt_min hc₀ hc₁, fun x => ⟨?_, ?_⟩⟩
  · have := (norm_nonneg (iteratedFDeriv ℝ 0 ρ 0)).trans (h₀ 0)
    have h2 : 0 ≤ C₀ * Real.exp (-c₀ * ‖(0 : Euc d)‖ ^ 2) := this
    simp at h2
    exact le_trans h2 (le_max_left _ _)
  · have h2 := h₀ x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
    have hC : 0 ≤ C₀ := by
      have := (norm_nonneg (iteratedFDeriv ℝ 0 ρ 0)).trans (h₀ 0)
      simpa using this
    have h3 : C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) ≤ max C₀ C₁ * Real.exp (-min c₀ c₁ * ‖x‖ ^ 2) := by
      refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (hC.trans (le_max_left _ _))
      nlinarith [min_le_left c₀ c₁, sq_nonneg ‖x‖]
    exact h2.trans h3
  · have h2 := h₁ x
    rw [norm_iteratedFDeriv_one] at h2
    have hC : 0 ≤ C₁ := by
      have := (norm_nonneg (iteratedFDeriv ℝ 1 ρ 0)).trans (h₁ 0)
      simpa using this
    have h3 : C₁ * Real.exp (-c₁ * ‖x‖ ^ 2) ≤ max C₀ C₁ * Real.exp (-min c₀ c₁ * ‖x‖ ^ 2) := by
      refine mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        (hC.trans (le_max_right _ _))
      nlinarith [min_le_right c₀ c₁, sq_nonneg ‖x‖]
    exact h2.trans h3

end HRS.MS.Wad
