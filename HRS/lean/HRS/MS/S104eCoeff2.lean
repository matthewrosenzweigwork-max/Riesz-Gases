import HRS.MS.S104eCoeff1
import HRS.MS.FcauTie
import HRS.MS.GoMeasAux2

/-!
# S10.4 (nonlinear), packet S104E-4: coefficient hypotheses (S.A.2/S.A.12 data) along a resulting solution, and uniqueness of classical adjoints

For every resulting solution `ρ` (small class or not: only `IsResultingSolution` and a thermal equilibrium are used), `2 ≤ d`, `0 ≤ s < d`, `a, β > 0`:
* `s104e_coeffHyp`: `CoeffHypRd s m Λ T0 ρ` for `m + 3 ≤ 100d + 1000`;
* `s104e_vhyp`, `s104e_regime`: `VHypRd (m+3)` of the confinement `a|x|²/2`, and a regime (R1 if `s ≤ d-2`, else R3 with `ν₀ = β⁻¹`);
* `s104e_unique`: `Fcau.propagatorW_eq` along the nonlinear coefficient: every classical adjoint solution `f` with terminal time `t ∈ [0,T0]` satisfies
  `propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t φ = f r` on `[0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r

variable {d : ℕ}

theorem s104e_coeffHyp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (m : ℕ) (hm : m + 3 ≤ 100 * d + 1000) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (T0 : ℝ) (hT0 : 0 ≤ T0) :
    ∃ Λ : ℝ, CoeffHypRd s m Λ T0 ρ := by
  obtain ⟨Λ, hΛ⟩ := s104e_regMF hd hs0 hsd ha hβ εstar c₁ C₁ (m + 3) hm hρβ hadm hres T0 hT0
  exact ⟨Λ, fun r hr => (hres.global T0).density r hr, hΛ, fun f hf hB =>
    (s104e_weak_cont hd hs0 hsd ha hβ hρβ hres hf hB).mono (fun r hr => hr.1)⟩

theorem s104e_vhyp (s a β : ℝ) (ha : 0 < a) (m : ℕ) :
    ∃ ΛV G₀ : ℝ, VHypRd (m + 3) ΛV G₀ (quadraticGradientDyn d s a β).V := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 (m + 3)
  refine ⟨ΛV, G₀, ?_⟩
  show VHypRd (m + 3) ΛV G₀ (confinement a)
  rw [HRS.MS.S21.s21_confinement_eq]
  exact hV

theorem s104e_regime (hd : 2 ≤ d) (s a β : ℝ) (hβ : 0 < β) :
    ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d s (quadraticGradientDyn d s a β).M
      (quadraticGradientDyn d s a β).invβ ν₀ := by
  by_cases h : s ≤ (d : ℝ) - 2
  · exact ⟨PDE.Regime.R1, 0, h⟩
  · refine ⟨PDE.Regime.R3, β⁻¹, ?_⟩
    show (d : ℝ) - 2 < s ∧ 0 < β⁻¹ ∧ β⁻¹ ≤ β⁻¹
    exact ⟨by linarith, inv_pos.2 hβ, le_rfl⟩

/-- Uniqueness of classical adjoint solutions along the nonlinear coefficient (every terminal time `t ∈ [0,T0]`). -/
theorem s104e_unique (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (T0 : ℝ) (hT0 : 0 ≤ T0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T0) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f) :
    ∀ r ∈ Icc (0 : ℝ) t, propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t φ = f r := by
  obtain ⟨Λ, hΛ⟩ := s104e_coeffHyp hd hs0 hsd ha hβ εstar c₁ C₁ 1 (by omega) hρβ hadm hres T0 hT0
  obtain ⟨ΛV, G₀, hV⟩ := s104e_vhyp (d := d) s a β ha 1
  obtain ⟨Rg, ν₀, hRg⟩ := s104e_regime hd s a β hβ
  exact HRS.MS.Fcau.propagatorW_eq (by omega) hs0 hsd 1 le_rfl Rg T0 Λ ΛV G₀
    (∑ i, ∑ j, |(quadraticGradientDyn d s a β).M i j|) β⁻¹ ν₀ (quadraticGradientDyn d s a β) ρ rfl
    (HRS.MS.Go.s55f_matBound _) hV ⟨(inv_pos.2 hβ).le, le_rfl⟩ hΛ hRg ht hf

end HRS.MS.S104e
