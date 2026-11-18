/-
# HRS.ME.FamV (packet V2): path bound along the rate family `V_θ = -θφ/β`, `θ ∈ [0,R]`

`rate_family_path_bound` is the uniform critical centered path estimate of
`HRS.ME.FamU.critical_centered_path_uniform_proved` (`HRS/ME/FamUFinal.lean`, the proved form of the frozen
`HRS.Main.critical_centered_path_uniform`) applied to the family `𝒱 = {V_θ : θ ∈ [0,R]}` with
`PotentialFamilyBounded 𝒱` from `HRS.ME.FamV.rateFamily_bounded` (`HRS/ME/FamVA.lean`), at the single
temperature `βm = βp = β`.  Its conclusion is the first conjunct, the `W₂` bound, with the same constant
`C` for all `θ ∈ [0,R]`, the Gibbs initial law `rateGibbs` and the stationary Gaussian field of `V_θ`.
-/
import HRS.ME.FamVA
import HRS.ME.FamUFinal

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamV

theorem rate_family_path_bound {d : ℕ} (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (R : ℝ) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ)
    (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) R, ∀ ρθ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β ρθ →
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ) T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = rateGibbs d ((d : ℝ) / 2) k β θ N →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → NegSobolev d m),
          IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd hβ (rateV k β θ) ρθ m Z →
          wassersteinE 2 (law P (HRS.Main.windowZeta m T 0 P X)) (law P' (HRS.Main.windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C, hC, h⟩ := HRS.ME.FamU.critical_centered_path_uniform_proved hd hs0 hsd
    {V : Torus d → ℝ | ∃ θ ∈ Set.Icc (0 : ℝ) R, V = HRS.rateV k β θ} (rateFamily_bounded k β R)
    β β hβ le_rfl m hm T hT
  refine ⟨C, hC, ?_⟩
  intro θ hθ ρθ hρ N hN Ω _ P _ X₀ W X hSF hFilt hLaw Ω' _ P' _ Z hG
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  have hSF' : SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd (HRS.rateV k β θ) β
      (hβ.trans_le hβI.1)) (0 + T) X₀ W X := by
    rw [zero_add]
    exact hSF
  exact (h (HRS.rateV k β θ) ⟨θ, hθ, rfl⟩ β hβI ρθ hρ 0 le_rfl N hN P X₀ W X hSF' hFilt hLaw P' Z hG).1

end HRS.ME.FamV
