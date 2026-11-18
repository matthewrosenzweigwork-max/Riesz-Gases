/-
# HRS.Equilibrium.TripleCanonical — packet Q84c: assembly of Lemma 4.15

`triple_canonical_proof` has the statement of the frozen `HRS.triple_canonical` (PairCorrection.lean),
proved by combining the size bounds `Q84a.q84a_estimates`, the canonicity `Q84b.q84b_canonical`, and
the symmetry lemmas `Q84.q84_Gpsi_symm`, `Q84.q84_Bpsi_symm` (NormalForm.lean).
-/
import HRS.Equilibrium.Q84aEstimates
import HRS.Equilibrium.Q84bCanonical
import HRS.Equilibrium.NormalForm

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

theorem triple_canonical_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ →
        IsSymmTriple (Gpsi d s ρ ψ) ∧ IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ) ∧
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
          C * K₁ * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
        IsSymmPair (Bpsi d s ρ ψ) ∧
        (∀ x y, x ≠ y → |Bpsi d s ρ ψ x y| ≤ C * K₁ * wEnv s x y ^ 2) := by
  obtain ⟨C, hC⟩ := Q84a.q84a_estimates hd hcrit β hβ V hV ρ hρ hρs
  refine ⟨C, fun f K₁ ψ hf hψ => ?_⟩
  obtain ⟨hG, hB⟩ := hC f K₁ ψ hf hψ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by
    rw [hcrit]
    linarith
  have hsymm : IsSymmPair ψ := hψ.symm
  exact ⟨Q84.q84_Gpsi_symm hsymm,
    Q84b.q84b_canonical hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ,
    hG, Q84.q84_Bpsi_symm hsd hsymm, hB⟩

example := (@triple_canonical_proof : type_of% @HRS.triple_canonical)

end HRS

end
