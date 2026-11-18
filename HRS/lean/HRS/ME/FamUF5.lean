import HRS.ME.ParxUAssembly3
import HRS.ME.PmU
import HRS.ME.EVUE2

/-!
# Chunk E, packet F5a (namespace `HRS.ME.FamU`): V-uniform parametrix bundle and pair-Poisson theorem

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`):
* `HRS.ME.ParxU.parxU_of_eqevo` (`HRS/ME/ParxU.lean:133`) becomes `parxU_of_eqevoV`. The data supply is
  `HRS.ME.EVU.eqevo_thermal_unifV` (EVUE2) with `Bv := Bf (K+2)`; the hypothesis on `V` is
  `IsSmooth V` and `∀ j, cbNorm j V ≤ Bf j`. The constants `c₀, Λ₀` are chosen before `V`.
* `HRS.ME.PmU.rhoU_exists` (`HRS/ME/PmU.lean`) becomes `rhoU_existsV`, with `1 ≤ Λ₀` before `V`.
* `HRS.ME.ParxU.pair_poisson_unif_thermal` (`HRS/ME/ParxUAssembly3.lean:24`) becomes
  `pair_poisson_unif_thermal_unifV`. The constant `C` comes from `pair_poisson_gen_unif`, which is already
  V-uniform, with the `c₀, Λ₀` of `parxU_of_eqevoV`; the proof is the original one plus `parxU_of_eqevoV`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.FamU

open HRS HRS.Parx

variable {d : ℕ}

/-- **F5.1 (V-uniform copy of `parxU_of_eqevo`).** For every level `n, K` with `2n+6d+30 ≤ K`, the
constants `c₀, Λ₀` are chosen before `V`, `β`, `ρ`; the bound `Bf` on the `C^j` norms of `V` is fixed
data. -/
theorem parxU_of_eqevoV (hd : 2 ≤ d) (s βm βp : ℝ) (hs : s = (d : ℝ) / 2) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∀ (n K : ℕ), 2 * n + 6 * d + 30 ≤ K →
      ∃ c₀ Λ₀ : ℝ, 0 < c₀ ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V →
        (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) → ∀ β : ℝ, β ∈ Icc βm βp → ∀ ρ : Torus d → ℝ,
        IsThermalDensity (periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
          HRS.ME.ParxU.ParxU d s n βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ := by
  intro n K hK
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, -, -, hmain⟩ :=
    HRS.ME.EVU.eqevo_thermal_unifV hd s βm βp hs0 hsd hβm hββ (Bf (K + 2)) n K hK
  refine ⟨c₀, Λ₀, hc₀, fun V hV hVB β hβ ρ hρ hsm hpos => ?_⟩
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hF := (hmain V hV (hVB (K + 2)) β hβ ρ hρ).1
  exact ⟨⟨hd, hs, hβpos, hV, hρ, ⟨hρ.1, hsm, hpos⟩⟩, hF⟩

/-- **F5.2 (V-uniform copy of `rhoU_exists`).** The constants `c₀, Λ₀` (with `1 ≤ Λ₀`) are chosen before
`V`, `β`, `ρ`, and every thermal density at `β ∈ [βm, βp]` satisfies `RhoU`. -/
theorem rhoU_existsV (hd : 2 ≤ d) (s βm βp : ℝ) (hs : s = (d : ℝ) / 2) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ c₀ Λ₀ : ℝ, 0 < c₀ ∧ 1 ≤ Λ₀ ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V →
      (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) → ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.IsThermalDensity (HRS.periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
        HRS.ME.PmU.RhoU d βm βp c₀ Λ₀ β ρ := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hs]; positivity
  obtain ⟨c₀, Λ₀, hc₀, hU⟩ := parxU_of_eqevoV hd s βm βp hs hs0 hsd hβm hββ Bf 0 (6 * d + 30)
    (by omega)
  refine ⟨c₀, max Λ₀ 1, hc₀, le_max_right _ _, fun V hV hVB β hβ ρ hρ hsm hpos => ?_⟩
  have U := hU V hV hVB β hβ ρ hρ hsm hpos
  exact ⟨hβm, hβ, hc₀, ⟨hρ.1, hsm, hpos⟩, U.rho_ge, fun x => (U.rho_le x).trans (le_max_left _ _)⟩

/-- **F5.3 (V-uniform copy of `pair_poisson_unif_thermal`).** The constant `C` is chosen before `V`; the
constants `c₀, Λ₀` of the bundle come from `parxU_of_eqevoV`, before `V`. -/
theorem pair_poisson_unif_thermal_unifV {s : ℝ} (hd : 2 ≤ d) (hs : s = (d : ℝ) / 2) (hs0 : 0 < s)
    (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
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
  obtain ⟨c₀, Λ₀, hc₀, hU⟩ := parxU_of_eqevoV hd s βm βp hs hs0.le hsd hβm hββ Bf n
    (2 * n + 6 * d + 30) le_rfl
  obtain ⟨C, hC0, hC⟩ := HRS.ME.ParxU.pair_poisson_gen_unif (N := n) (νm := βp⁻¹) (νp := βm⁻¹)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hs hn5 hn7 hn1 (8 * d + 80) (by unfold parxK parxJ; omega)
  refine ⟨C, hC0, fun V hV hVB β hβ ρ hρ hsm hpos => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hC β V ρ (hU V hV hVB β hβ ρ hρ hsm hpos)
  exact ⟨Ψ, hΨ⟩

end HRS.ME.FamU

end
