import HRS.Uniform.Q48bAux1
import HRS.Uniform.Evolution

/-!
# Q48b, part 2: Proposition 5.2 for the stationary path

Specialisation of `HRS.PDE.adjoint_decay_comparison` to the constant path `ρ^t ≡ ρβ` (a solution of the mean-field
equation by part 1): the decay of the centered adjoint propagator in `H^j`, for every even integer `j > d/2 + 4`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q48b

open HRS HRS.PDE

variable {d : ℕ}

theorem q48b_prop52 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ φ : Torus d → ℝ, Continuous φ → MemSobolev (j : ℝ) φ →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t →
        MemSobolev (j : ℝ) (projMean (withDensityReal ρβ)
          (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ)) ∧
        sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ)
          (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ)) ≤
          C * Real.exp (-c * (t - u)) * sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) := by
  set K : ℕ := 2 * j + 4 * d + 20 with hKdef
  have hKr : (d : ℝ) / 2 + 6 < K := by
    have : (2 * j + 4 * d + 20 : ℕ) = (K : ℕ) := rfl
    rw [hKdef]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have H := q48b_finiteRegHyp s hs0 hsd β hβ V hV ρβ hth hρ hpos K hKr
  obtain ⟨C, c, κ, hC, hc, hκ, h⟩ := adjoint_decay_comparison hd s β β K V ρβ H j hj hjd le_rfl
  refine ⟨C, c, hC, hc, fun φ hφc hφ u t hu hut => ?_⟩
  have hsol := q48b_isMFSolutionHK hd s hs0 hsd β hβ V hV ρβ hth hρ hpos K
  have := h β ⟨le_rfl, le_rfl⟩ (fun _ => coeffOf ρβ) hsol ρβ hth (q48b_continuous_of_isSmooth hρ)
    hpos φ hφc hφ u t hu hut
  rw [q48b_mfPath_const ρβ hρ] at this
  exact ⟨this.1, this.2.1⟩

end HRS.Uniform.Q48b
