import HRS.MS.SA16U3K9a
import HRS.MS.SA16U3K9b

/-!
# S.A.16 K9: `splice_screened_low` (worker SA16U3)

Assembly of `sa16u3_screened_lt_one` (`0 < θ < 1`, HLS) and `sa16u3_screened_one` (`θ = 1`, uniform CZ bound plus
Young for the Coulomb core).  The statement is copied verbatim from `SA16-COMPATIBLE-CUTOFF.lean`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA

/-- K9: screened bounds for the compatible operator below and at theta=1. -/
theorem splice_screened_low (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hp : 2 ≤ p)
    (hfar : θ < 1 → 1/p+(1-θ)/(d : ℝ)<1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i : Fin d,
      ∀ a W : Euc d → ℝ,
      MemLp a (if θ=1 then ⊤ else ENNReal.ofReal ((d : ℝ)/(1-θ))) volume →
      MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (spliceOdd d θ δ i (fun y => a y*W y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C*
          eLpNorm a (if θ=1 then ⊤ else ENNReal.ofReal ((d : ℝ)/(1-θ))) volume*
          eLpNorm W (ENNReal.ofReal p) volume := by
  rcases hθ1.lt_or_eq with hlt | heq
  · obtain ⟨C, hC, h⟩ := sa16u3_screened_lt_one d hd θ p hθ0 hlt hp (hfar hlt)
    refine ⟨C, hC, fun δ hδ i a W ha hW => ?_⟩
    simp only [if_neg hlt.ne] at ha ⊢
    exact h δ hδ i a W ha hW
  · subst heq
    obtain ⟨C, hC, h⟩ := sa16u3_screened_one d hd p hp
    refine ⟨C, hC, fun δ hδ i a W ha hW => ?_⟩
    simp only [if_true] at ha ⊢
    exact h δ hδ i a W ha hW

end HRS.Whole.AppendixA.Phase2SA16Cutoff
