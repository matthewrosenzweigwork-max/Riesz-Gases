import HRS.MC.S7FCF5EA
import HRS.MC.S7FCF5EB
import HRS.MC.S7FCF5Defs

/-!
# FC-E start-`a` packet, part F (G1): the particle pair `pairN` is `AEMeasurable` for every window start `a ≥ 0`

`fcf5_G1_pair_aemeasurable_proof`: the statement of `HRS.MC.Sec7.FCF5Plan.fcf5_G1_pair_aemeasurable` (copied verbatim,
checked in `HRS/MC/S7FCF5ETie.lean`), proved from the zeta component `S7FCF5E_aemeasurable_zetaWin` (part A) and the
centred quadratic component `S7FCF5E_aemeasurable_quadField` (part B).  The case `a = 0` is
`HRS.MC.Sec7.S7FCW12.s7_FC_E_pair_measurable_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

namespace HRS.MC.Sec7.S7FCF5E

variable {d : ℕ}

theorem fcf5_G1_pair_aemeasurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) (a : ℝ) (ha : 0 ≤ a) :
    AEMeasurable (pairN r T a R.D.s R.ρ P X) P := by
  have hS := hreal.solution T
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  unfold pairN
  exact AEMeasurable.prodMk (S7FCF5E_aemeasurable_zetaWin r T a hT hm P X hS.adapted hS.cont hN0)
    (S7FCF5E_aemeasurable_quadField R r T hT a ha P X hS.adapted hS.cont)

end HRS.MC.Sec7.S7FCF5E

end
