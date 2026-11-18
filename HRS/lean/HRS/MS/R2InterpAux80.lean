import HRS.MS.R2InterpAux79
import HRS.MS.R2InterpAux74
import HRS.MS.GenPathAux27

/-!
# S10.2 (worker S102), part 80 (packet F5): the duality identity for the Hermite orbits under the thermal quadratic dynamics

`DualityIdentityRd` for `f_r = U^{r,t}φ_α` (`φ_α = oscTestFun m α`) along the filtered strong solution: all hypotheses of `s56_duality_core` are discharged for
the stationary quadratic coefficient (thermal density, `ν = β⁻¹`, `V = a|x|²/2`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

theorem s102_duality (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (m : ℝ) (α : MultiIndex d) :
    DualityIdentityRd P ℱ W' (quadraticGradientDyn d s a β) (fun _ => ρ) X t
      (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t (oscTestFun m α)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by simp [Matrix.IsSymm]
  obtain ⟨Λ, hΛ⟩ := HRS.MS.UlW.ulw_coeffHyp hd hs0 hsd 0 hρS.1 hρS.2 T
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ (quadraticGradientDyn d s a β).V := by
    show VHypRd 2 ΛV G₀ (confinement a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  have hMF : IsWholeMeanFieldSolution (quadraticGradientDyn d s a β) T (fun _ => ρ) := by
    rw [HRS.MS.S21.s21_dyn_eq]
    exact HRS.MS.S21.s21_mf_stationary hd hs0 hsd ha hβ hρ T
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t
      (oscTestFun m α) f₀ := by
    obtain ⟨g, hg⟩ := s102_osc_schwartz m α
    have := s102_exists_adjoint hd hs0 hs ha hβ hρ hT g ht
    rw [hg] at this
    exact this
  have hf := s102_propagator_classical ⟨f₀, hf₀⟩
  exact HRS.MS.GenPath.s56_duality_core s Λ T ΛV G₀ (quadraticGradientDyn d s a β) rfl hs0 hsd
    (inv_pos.2 hβ).le hVD (fun _ => ρ) hMF hΛ.regular P X₀ W X hX ℱ W' hF t ht (oscTestFun m α) _ hf

end HRS.MS.R2Interp

end
