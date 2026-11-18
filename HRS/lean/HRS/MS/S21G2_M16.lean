import HRS.MC.E213U15a
import HRS.MS.R2InterpAux4

/-!
# S21G2 M16 -- unit-ball preservation and derivative formula for the heat function (R26-T3.M16)

`y ↦ ∫ Φ(y + Γ) dP` stays in the `C_b^5` unit ball for every `Φ` there and every strongly measurable
`Γ : Ω → B`, with `D^j` computed under the integral.  Reduction to the merged `s102_heat_derivs` for the
law `P.map Γ`.  The contract is taken verbatim.  Helper names carry the prefix `s21g2_m16_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

def r26t3_heat {B : Type*} [NormedAddCommGroup B] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Γ : Ω → B) (Φ : B → ℝ) (y : B) : ℝ := ∫ ω, Φ (y+Γ ω) ∂P

theorem r26t3_heat_bounds {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Γ : Ω → B) (hΓ : AEStronglyMeasurable Γ P) (Φ : B → ℝ) (hΦ : Φ∈CbUnitBall B 5) :
    r26t3_heat P Γ Φ∈CbUnitBall B 5 ∧
      ∀ j≤5, ∀ y, iteratedFDeriv ℝ j (r26t3_heat P Γ Φ) y=
        ∫ ω, iteratedFDeriv ℝ j Φ (y+Γ ω) ∂P := by
  have hmΦ : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  haveI : IsProbabilityMeasure (P.map Γ) := (Measure.isProbabilityMeasure_map_iff hΓ.aemeasurable).2 inferInstance
  have hcomp : ∀ (F : B → ℝ), Continuous F → ∀ y : B,
      ∫ ω, F (y + Γ ω) ∂P = ∫ z, F (y + z) ∂(P.map Γ) := fun F hF y => by
    exact (integral_map (f := fun z => F (y + z)) hΓ.aemeasurable
      (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable).symm
  have hheat : r26t3_heat P Γ Φ = fun y => ∫ z, Φ (y + z) ∂(P.map Γ) :=
    funext fun y => hcomp Φ hΦ.1.continuous y
  obtain ⟨hcd, hd⟩ := HRS.MS.R2Interp.s102_heat_derivs (P.map Γ) hmΦ
  have hform : ∀ j ≤ 5, ∀ y, iteratedFDeriv ℝ j (r26t3_heat P Γ Φ) y =
      ∫ ω, iteratedFDeriv ℝ j Φ (y + Γ ω) ∂P := fun j hj y => by
    rw [hheat, (hd j hj y).1]
    exact (integral_map (f := fun z => iteratedFDeriv ℝ j Φ (y + z)) hΓ.aemeasurable
      ((hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable)
  refine ⟨⟨by rw [hheat]; exact hcd, fun j hj => ?_, ?_⟩, hform⟩
  · refine ⟨⨆ z, ‖iteratedFDeriv ℝ j Φ z‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    rw [hheat]; exact (hd j hj y).2
  · unfold cbNorm
    refine le_trans (Finset.sum_le_sum fun j hj => ?_) hΦ.2.2
    refine ciSup_le fun y => ?_
    rw [hheat]
    exact (hd j (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj) y).2

end HRS.MS.R26T3
