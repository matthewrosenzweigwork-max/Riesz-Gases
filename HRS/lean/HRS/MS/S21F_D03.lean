import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.D03: monotonicity of the physical radius

A trajectory for radius `δ` is a trajectory (same physical data) for every larger radius `ε ≥ δ`, provided `0 ≤ C₁`.
Only the radius in the smallness and the resulting weighted/velocity bounds is increased.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_trajectory_weaken {p : Parameters} {δ ε : ℝ} (hδ : 0 < δ) (hε : δ ≤ ε)
    (R : Trajectory p δ) (hC : 0 ≤ p.C₁) :
    ∃ R' : Trajectory p ε, R'.ρβ = R.ρβ ∧ R'.ε = R.ε ∧ R'.ψ = R.ψ ∧ R'.ρ = R.ρ := by
  have _ := hδ
  have hA := R.admissible
  have hR := R.resulting
  have hCe : ∀ t : ℝ, p.C₁ * δ * Real.exp (-p.c₁ * t) ≤ p.C₁ * ε * Real.exp (-p.c₁ * t) := fun t =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε hC) (Real.exp_pos _).le
  refine ⟨⟨R.ρβ, R.thermal, R.ε, R.ψ,
    ⟨hA.smooth, hA.compactSupport, hA.nonzero, hA.meanZero, hA.small.trans hε⟩, R.ρ,
    ⟨hR.cpos, hR.global, hR.init, hR.ratio,
      fun t ht => ⟨(hR.weighted t ht).1, (hR.weighted t ht).2.trans (hCe t)⟩,
      fun t ht => (hR.velocity t ht).trans (ENNReal.ofReal_le_ofReal (hCe t)),
      hR.cont, hR.regular⟩⟩, rfl, rfl, rfl, rfl⟩

end HRS.MS.R26T3
