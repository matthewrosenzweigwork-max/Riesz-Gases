import HRS.MS.S104bNL6

/-!
# S10.5 (nonlinear), packet S104b-NL7: the moving window data `S21mData` along a resulting solution

`S105nReg`: the mean-field regularity `IsRegularMFRd s 3 Λ T ρ` (C_b^3 and the `⟨x⟩^{d+3}`-weighted bounds of `ρ^t`, and the singular force bound for `s ≥ d-1`) of the resulting
solutions of the class; it is an analytic input (consequence of the `Σ^{102d+1020}` and `C_b^{100d+1000}` bounds of `IsResultingSolution`; not in the repository).
`s104b_mfData`: `MFData` for the quadratic dynamics from it.  `s104b_oscAdj`: `OscAdjointInput` from the terminal-time regularity `S104nOrbit` and the orbit bounds.
`s104b_data`: `S21mData d s a β T b ρ` for every window start `b ≥ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S53 HRS.MS.R2WinErr HRS.MS.R2GenInit HRS.MS.S21m HRS.MH.DualityRd

variable {d : ℕ}

/-- The regularity of the resulting solutions of the class in the sense of `IsRegularMFRd` (an analytic input). -/
def S105nReg (d : ℕ) (s a β εstar c₁ C₁ : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ T0 : ℝ, 0 ≤ T0 → ∃ Λ : ℝ, IsRegularMFRd s 3 Λ T0 ρ

theorem s104b_mfData {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (ha : 0 < a) {εstar ε c₁ C₁ T0 Λ : ℝ}
    {ρβ : Euc d → ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (hreg : IsRegularMFRd s 3 Λ T0 ρ) :
    ∃ ΛV G₀ : ℝ, MFData s Λ T0 ΛV G₀ (quadraticGradientDyn d s a β) ρ := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ (quadraticGradientDyn d s a β).V := by
    show VHypRd 2 ΛV G₀ (confinement a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  exact ⟨ΛV, G₀, ⟨rfl, hs0, hsd, (inv_pos.2 hβ).le, hVD, hres.global T0, hreg⟩⟩

end HRS.MS.S104b
