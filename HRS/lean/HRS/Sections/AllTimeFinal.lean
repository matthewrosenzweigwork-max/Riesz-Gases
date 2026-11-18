import HRS.Sections.AllTimeAux2

/-!
# ALLTIME: Lemma 7.8 `alltime_Lp` (`M:U:lem:alltime-Lp`), relocated proof

Chain plan: header of `AllTimeAux1.lean`.  Item 1 is `alltime_item1` (via `mov_lp_bound`, hence conditional on the
MOV statements), items 2 and 3 are `alltime_item2`, `alltime_item3` (pressure estimates, uniform in `t`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Sec7

variable {d : ℕ}

theorem alltime_Lp_proof (R : Regime d) (c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c) :
    (∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t →
          (P.map (X t.toNNReal)) ≪ modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))))
            (ENNReal.ofReal p)
            (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ≪
          Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)) ∧
        eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))).rnDeriv
            (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)))) (ENNReal.ofReal q)
          (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C) ∧
    (∀ B : ℝ, ∃ cB CB : ℝ, 0 < cB ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c)) →
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (cB * N *
            |modulatedEnergy h X (withDensityReal (R.ρ t))|))
          ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤
          ENNReal.ofReal CB) :=
  ⟨alltime_item1 R, alltime_item2 R, alltime_item3 R c hc⟩

example := (@alltime_Lp_proof : type_of% @HRS.Sec7.alltime_Lp)

end Sec7

end HRS

end
