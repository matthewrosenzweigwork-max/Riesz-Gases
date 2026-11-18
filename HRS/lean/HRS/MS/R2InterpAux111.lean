import HRS.MS.R2InterpAux110
import HRS.MS.R2InterpAux74
import HRS.MS.R2InterpAux78

/-!
# S10.2 (worker S10R), part 111: assembly of `S102Part` from the proved packets and the three open items (`S102Rest`)

`S102Rest` collects what is NOT yet proved (handoff `HANDOFF_S10R.md`): (M1) the drift structure `S102Drift` with integrable `∫ Mb`, and (M3) continuity of the predicted path `Y`
in `𝓧`.  Everything else of `S102Part` is proved (F5 `s102_itoRep`, M2 `s102_M2`, M3 measurability, `hzi`, the measurability of `∫ cylA`, `∫ cylJ`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

set_option maxSynthPendingDepth 3 in
/-- The two open items of `S102Part`. -/
def S102Rest {d : ℕ} (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw sQ : ℝ) (μ : Measure (Euc d)) (hT : 0 < T) {N : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) : Prop :=
  (∃ Mb : Ω → ℝ → ℝ, (∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField sQ μ P X u ζ) (Mb ζ)) ∧
    Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P) ∧
  (∀ᵐ ζ ∂P, ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T))

end HRS.MS.R2Interp

end
