import HRS.ME.UIPath
import HRS.ME.UIPathTightP6

/-!
# Packet Q5a of `HRS.ui_path_shifted`: tightness of the shifted subfamily

Proves `shifted_family_tight` (statement copied verbatim from `HRS/ME/UIPathShiftedSpec.lean`).
The family of window laws along any starts `u n ≥ 0` is a subset of the family of `ui_path_tight`,
which is tight by `HRS.ME.UIPathTight.p6_assembly`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- **Q5a** (tightness of the shifted subfamily; scope note Q5).  The laws of the windows along ANY window starts
`u_n ≥ 0` form a tight family: they are a subset of the family of `ui_path_tight`.  (`u_n → ∞` is not needed
here.)  Route: `HRS.ME.UIPathTight.p6_assembly` (= `ui_path_tight`) and `IsTightMeasureSet.subset`
(the range `{(S.P n).map (windowGibbs … (u n) …)}` is contained in the set of `ui_path_tight`). -/
theorem shifted_family_tight (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) :
    IsTightMeasureSet (Set.range fun n =>
      (S.P n).map (windowGibbs m T (u n)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n))) := by
  have h6 := HRS.ME.UIPathTight.p6_assembly hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI m hm
  refine IsTightMeasureSet.subset h6 ?_
  rintro μ ⟨n, rfl⟩
  exact ⟨n, u n, hu0 n, rfl⟩

end HRS.ME.UIPathShifted
