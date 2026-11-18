import HRS.MD.Stat

/-!
# EQ-LZ packet MARG: stationarity of the Gibbs-started flow (`eqlz_marg`), proof

`eqlz_marg` is the real-time form (`0 ≤ t ≤ T`, `law P (X t.toNNReal)`) of the already proved
`HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof` (`B.15` free branch: entropy dissipation from the Gibbs start;
`gibbsRef = canonicalGibbs`).  The case `T = 0` is inside that proof (`X 0 = X₀` a.s.).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

namespace MD

namespace EQLZMarg

/-- (MARG, `eqlz_marg`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_marg`. -/
theorem eqlz_marg_proof :
    ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T : ℝ),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X →
        ∀ t : ℝ, 0 ≤ t → t ≤ T → law P (X t.toNNReal) = canonicalGibbs (periodicRiesz d s) V N β := by
  intro d N hd hN s hs0 hsd V hV β hβ T Ω _ P _ X₀ W X h t ht0 htT
  have key := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ T hN P X₀ W X h
    t.toNNReal (by rw [Real.coe_toNNReal t ht0]; exact htT)
  simpa [law] using key

end EQLZMarg

end MD

end HRS

end
