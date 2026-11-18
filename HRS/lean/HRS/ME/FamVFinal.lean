/-
# HRS.ME.FamV (packet V4): upper bounds of `critical_family_path_sup` and `critical_family_sharpness`

`critical_family_path_sup_upper` is the second conjunct of the frozen `HRS.Main.critical_family_path_sup`
(`HRS/Main/HeadlineEquilibrium.lean:345`) with the same hypotheses and the same quantifiers, except that the constant `C` is
stated on its own and the threshold `N₀` is `2`.  It follows termwise from `rate_family_path_bound` (packet V2): the
supremum over `θ ∈ [0,R]` is at most a common bound of the terms.
-/
import HRS.ME.FamVB

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamV

theorem critical_family_path_sup_upper {d : ℕ} (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m)
    (T : ℝ) (hT : 0 < T) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ (Ω : ℝ → Type) [∀ θ, MeasurableSpace (Ω θ)] (P : ∀ θ, Measure (Ω θ))
        [∀ θ, IsProbabilityMeasure (P θ)] (X₀ : ∀ θ, Ω θ → Config d N)
        (W : ∀ θ, ℝ≥0 → Ω θ → (Fin N → Euc d)) (X : ∀ θ, ℝ≥0 → Ω θ → Config d N),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        SelectedFlow (P θ) (PDE.mfData d ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ) T
          (X₀ θ) (W θ) (X θ) ∧ law (P θ) (X₀ θ) = rateGibbs d ((d : ℝ) / 2) k β θ N) →
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω θ)))
          (W' : ℝ≥0 → Ω θ → (Fin N × Fin d) → ℝ), IsFilteredSolution (P θ) ℱ W' (W θ) (X θ)) →
      ∀ (Ω' : ℝ → Type) [∀ θ, MeasurableSpace (Ω' θ)] (P' : ∀ θ, Measure (Ω' θ))
        [∀ θ, IsProbabilityMeasure (P' θ)] (Z : ∀ θ, ℝ → Ω' θ → NegSobolev d m),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        IsStationaryGaussianField (P' θ) ((d : ℝ) / 2) β hs0 hsd hβ (rateV k β θ) (ρ θ) m (Z θ)) →
        (⨆ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (law (P θ) (HRS.Main.windowZeta m T 0 (P θ) (X θ)))
              (law (P' θ) (HRS.Main.windowPath m T 0 (Z θ)))) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C, hC, h⟩ := rate_family_path_bound hd hs0 hsd β hβ k
    (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)) m hm T hT
  refine ⟨C, hC, fun N hN Ω _ P _ X₀ W X hflow hfilt Ω' _ P' _ Z hZ => ?_⟩
  refine iSup₂_le fun θ hθ => ?_
  exact h θ hθ (ρ θ) (hρ θ) N hN (P θ) (X₀ θ) (W θ) (X θ) (hflow θ hθ).1 (hfilt θ hθ)
    (hflow θ hθ).2 (P' θ) (Z θ) (hZ θ hθ)

end HRS.ME.FamV
