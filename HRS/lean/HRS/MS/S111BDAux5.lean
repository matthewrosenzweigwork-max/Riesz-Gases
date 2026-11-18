import HRS.Whole.Window
import HRS.MS.TensRelAux1

/-!
# S11.1 packet D1: Riesz assembly of the frozen cross-density family
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111BD

open HRS HRS.Whole

theorem s111_cross_densities_of_functionals
    (d : ℕ) (s a β γ : ℝ) (ρ : Euc d → ℝ) (T u : ℝ)
    (hu : 0 ≤ u) (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x)
    (S : Submodule ℝ (Euc d → ℝ))
    (hS : ∀ ψ ∈ S, MemLp ψ 2 (HRS.Whole.withDensityReal ρ))
    (hdom : ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ → ψ ∈ S)
    (hcov : ∀ (r : ℝ), 0 ≤ r → ∀ (t : ℝ), 0 ≤ t →
      ∀ φ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) φ →
      ∃ (ℓ : S →ₗ[ℝ] ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ ψ : S, |ℓ ψ| ≤ B * ‖HRS.MS.TensRel.s111_toLp S hS ψ‖) ∧
        ∀ ψ : S, ℓ ψ = HRS.Whole.linearGaussianCov
          ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
          (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ)
          r t (ψ : Euc d → ℝ) φ) :
    R2CrossDensitiesExist d s a β γ ρ T u := by
  classical
  intro τ φ hφ
  have key : ∀ (i : Fin 3) (r : ℝ), ∃ χ : Euc d → ℝ, r ∈ Set.Icc (0 : ℝ) (u + T) →
      MemLp (fun x => χ x / ρ x) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
        Integrable (fun x => ψ' x * χ x) ∧
        ∫ x, ψ' x * χ x = HRS.Whole.linearGaussianCov
          ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
          (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ) r (u + τ i)
            ψ' (φ i) := by
    intro i r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (u + T)
    · obtain ⟨ℓ, B, -, hB, hℓ⟩ := hcov r hr.1 (u + (τ i : ℝ)) (by linarith [(τ i).2.1])
        (φ i) (hφ i)
      obtain ⟨χ, hχ1, hχ2⟩ := HRS.MS.TensRel.s111_density_of_l2_bound hρm hρpos S hS ℓ B hB
      refine ⟨χ, fun _ => ⟨hχ1, fun ψ' hψ' => ?_⟩⟩
      obtain ⟨h1, h2⟩ := hχ2 ⟨ψ', hdom ψ' hψ'⟩
      exact ⟨h1, h2.trans (hℓ ⟨ψ', hdom ψ' hψ'⟩)⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose χ hχ using key
  exact ⟨fun i r => χ i r, fun i r hr => hχ i r hr⟩

/-- The open core X1 (L2 covariance functional), as a proposition. -/
def S111CovCore (d : ℕ) (s a β γ : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ∃ S : Submodule ℝ (Euc d → ℝ),
    ∃ hS : ∀ ψ ∈ S, MemLp ψ 2 (HRS.Whole.withDensityReal ρ),
      Measurable ρ ∧ (∀ x, 0 < ρ x) ∧
      (∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ → ψ ∈ S) ∧
      ∀ (r : ℝ), 0 ≤ r → ∀ (t : ℝ), 0 ≤ t →
        ∀ φ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) φ →
        ∃ (ℓ : S →ₗ[ℝ] ℝ) (B : ℝ), 0 ≤ B ∧
          (∀ ψ : S, |ℓ ψ| ≤ B * ‖HRS.MS.TensRel.s111_toLp S hS ψ‖) ∧
          ∀ ψ : S, ℓ ψ = HRS.Whole.linearGaussianCov
            ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
            (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
              (HRS.Whole.withDensityReal ρ) γ)
            r t (ψ : Euc d → ℝ) φ

/-- `r2_cross_density_exists` from the open core X1 (conditional). -/
theorem r2_cross_density_exists_of_core
    (hX1 : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < (d : ℝ) / 2 → ∀ (a β γ : ℝ), 0 < a → 0 < β →
      0 ≤ γ → (0 < s → 0 < γ) → ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
        S111CovCore d s a β γ ρ) :
    type_of% @HRS.Whole.r2_cross_density_exists := by
  intro d hd s hs0 hs a β γ ha hβ hγ hγs T ρ hρ u hu
  obtain ⟨S, hS, hρm, hρpos, hdom, hcov⟩ := hX1 d hd s hs0 hs a β γ ha hβ hγ hγs ρ hρ
  exact s111_cross_densities_of_functionals d s a β γ ρ T u hu hρm hρpos S hS hdom hcov

end HRS.MS.S111BD
