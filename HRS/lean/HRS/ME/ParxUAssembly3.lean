import HRS.ME.ParxUAssembly2

/-!
# Packet P7 (assembly), part (c): the uniform pair-Poisson theorem for thermal densities

`pair_poisson_unif_thermal` is the uniform form of `HRS.pair_poisson_proof` (Assembly.lean:200):
for `d ≥ 2`, `s = d/2`, a smooth potential `V` and `0 < βm ≤ βp`, one constant `C` works for every
`β ∈ [βm, βp]` and every smooth positive thermal density `ρ`. The bundle `ParxU` for these `ρ` comes
from `parxU_of_eqevo` with a level `n` large enough for the hypotheses of `pair_poisson_gen_unif`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ}

/-- **Uniform `pair_poisson`** for thermal densities (part (c)). -/
theorem pair_poisson_unif_thermal (hd : 2 ≤ d) (hs : s = (d : ℝ) / 2) (hs0 : 0 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
      ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ),
        (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
          Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
        ∀ f : Torus d → ℝ, Torus.IsSmooth f →
          IsPairCorrector d s V β ρ f (C * posSeminorm (8 * d + 80) f) (Ψ f) ∧
          (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
          eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤
            ENNReal.ofReal (C * posSeminorm (8 * d + 80) f) := by
  obtain ⟨n, hn5, hn7, hn1⟩ : ∃ n : ℕ, px5m d (parxJ d) ≤ n ∧
      HRS.PDE.PX7.px7_m d + 2 + HRS.PDE.mStar d + 3 ≤ n ∧ 1 ≤ n :=
    ⟨px5m d (parxJ d) + (HRS.PDE.PX7.px7_m d + 2 + HRS.PDE.mStar d + 3) + 1,
      by omega, by omega, by omega⟩
  obtain ⟨c₀, Λ₀, hc₀, hU⟩ := parxU_of_eqevo hd s βm βp hs hs0.le hsd hβm hββ V hV n
    (2 * n + 6 * d + 30) le_rfl
  obtain ⟨C, hC0, hC⟩ := pair_poisson_gen_unif (N := n) (νm := βp⁻¹) (νp := βm⁻¹) (c₀ := c₀)
    (Λ₀ := Λ₀) hd hs0 hsd hs hn5 hn7 hn1 (8 * d + 80) (by unfold parxK parxJ; omega)
  refine ⟨C, hC0, fun β hβ ρ hρ hsm hpos => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hC β V ρ (hU β hβ ρ hρ hsm hpos)
  exact ⟨Ψ, hΨ⟩

end HRS.ME.ParxU

end
