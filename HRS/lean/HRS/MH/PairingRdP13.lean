import HRS.MH.PairingRdDefs
import HRS.Whole.Q09AAux2

/-!
# PairingRd packet PR13 (`pairing_identity_rd`): the abstract assembly

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route (torus lines `HRS/Duality/PairingExpansion.lean:742-:763`):
Fubini (`integral_prod`) on `μ ⊗ μ` and `μ_N ⊗ μ` with the fibre identity `hint`, `pair_empirical` for `∫ φ dμ_N`,
`integral_prod_swap` with the symmetry for `B(μ,μ_N) = B(μ_N,μ)`, then a linear combination.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR13** `pairing_identity_rd` (proof). -/
theorem pairing_identity_rd {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) (f : Euc d → ℝ) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hN : 0 < N) (X : Whole.EucConfig d N) (φ₁ φ₂ : Euc d → ℝ)
    (hK1 : Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)))
    (hK2 : Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2)
      ((Whole.empirical X).prod (Whole.withDensityReal ρ)))
    (hsymm : ∀ x y, pairKernelRdB f M s y x = pairKernelRdB f M s x y)
    (hint : ∀ x, ∫ y, pairKernelRdB f M s x y ∂(Whole.withDensityReal ρ) = (1 / 2 : ℝ) * (φ₁ x - φ₂ x))
    (hφ1 : Integrable φ₁ (Whole.withDensityReal ρ)) (hφ2 : Integrable φ₂ (Whole.withDensityReal ρ))
    (hφ1N : Integrable φ₁ (Whole.empirical X)) (hφ2N : Integrable φ₂ (Whole.empirical X)) :
    pairBRd f M s (Whole.empirical X) (Whole.empirical X) - pairBRd f M s (Whole.withDensityReal ρ) (Whole.withDensityReal ρ) =
      pairEmpRd φ₁ X (Whole.withDensityReal ρ) - pairEmpRd φ₂ X (Whole.withDensityReal ρ) +
        pairBSignedRd f M s (Whole.empirical X) (Whole.withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := Whole.Q09A.measure_isProb hρ
  haveI : IsProbabilityMeasure (Whole.empirical X) := Whole.empirical_isProbabilityMeasure hN X
  -- `B(μ, μ) = ½ (∫φ₁ dμ - ∫φ₂ dμ)`
  have hBmm : pairBRd f M s (Whole.withDensityReal ρ) (Whole.withDensityReal ρ)
      = (1 / 2 : ℝ) * (∫ x, φ₁ x ∂(Whole.withDensityReal ρ) - ∫ x, φ₂ x ∂(Whole.withDensityReal ρ)) := by
    unfold pairBRd
    rw [integral_prod _ hK1]
    calc ∫ x, ∫ y, pairKernelRdB f M s x y ∂(Whole.withDensityReal ρ) ∂(Whole.withDensityReal ρ)
        = ∫ x, (1 / 2 : ℝ) * (φ₁ x - φ₂ x) ∂(Whole.withDensityReal ρ) :=
          integral_congr_ae (Filter.Eventually.of_forall hint)
      _ = _ := by rw [integral_const_mul, integral_sub hφ1 hφ2]
  -- `B(μ_N, μ) = ½ (N⁻¹ ∑ φ₁(x_i) - N⁻¹ ∑ φ₂(x_i))`
  have e1 : ∫ x, φ₁ x ∂(Whole.empirical X) = (N : ℝ)⁻¹ * ∑ i, φ₁ (X i) :=
    Whole.pair_empirical hN X φ₁
  have e2 : ∫ x, φ₂ x ∂(Whole.empirical X) = (N : ℝ)⁻¹ * ∑ i, φ₂ (X i) :=
    Whole.pair_empirical hN X φ₂
  have hBNm : pairBRd f M s (Whole.empirical X) (Whole.withDensityReal ρ)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, φ₁ (X i) - (N : ℝ)⁻¹ * ∑ i, φ₂ (X i)) := by
    unfold pairBRd
    rw [integral_prod _ hK2]
    calc ∫ x, ∫ y, pairKernelRdB f M s x y ∂(Whole.withDensityReal ρ) ∂(Whole.empirical X)
        = ∫ x, (1 / 2 : ℝ) * (φ₁ x - φ₂ x) ∂(Whole.empirical X) :=
          integral_congr_ae (Filter.Eventually.of_forall hint)
      _ = _ := by rw [integral_const_mul, integral_sub hφ1N hφ2N, e1, e2]
  -- `B(μ, μ_N) = B(μ_N, μ)` by swapping and symmetry
  have hBmN : pairBRd f M s (Whole.withDensityReal ρ) (Whole.empirical X)
      = pairBRd f M s (Whole.empirical X) (Whole.withDensityReal ρ) := by
    unfold pairBRd
    rw [← integral_prod_swap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact hsymm p.1 p.2
  unfold pairBSignedRd pairEmpRd
  linear_combination (-2 : ℝ) * hBmm + 2 * hBNm + hBmN

end HRS.MH.PairingRdP
