import HRS.Dynamics.Setup
import HRS.Stochastic.Particle

/-!
# Proposition B.1 `M:B:thm:particle-wp`: collision-free strong well-posedness

Source: HRS periodic main paper, lines 11645-11656. The statement was moved unchanged from
`HRS.Dynamics.Setup`, because its proof (`particle_wellposed_proof`, package PART-01) lives in
`HRS/Stochastic/Particle.lean`, which imports `HRS.Dynamics.Setup`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Proposition B.1 `M:B:thm:particle-wp` (lines 11645-11656): for `N ≥ 2`, `0 ≤ s < d`,
`Sym M ≤ 0`, `V ∈ C²(𝕋^d)`, a.s. pairwise distinct `X₀` independent of `W`, and `d ≥ 2`
(case (i); cases (ii)-(iii) with `d = 1` are not covered by the main paper's torus setting
`d ≥ 2` and are stated separately in package PART-01), the system admits a pathwise unique
global collision-free strong solution. -/
theorem particle_wellposed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (hd : 2 ≤ d) (hN : 2 ≤ N) (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V)
    (X₀ : Ω → Config d N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P) (T : ℝ) (hT : 0 < T) :
    (∃ X, IsStrongSolution P D T X₀ W X) ∧ PathwiseUnique P D T X₀ W := by
  exact particle_wellposed_proof P D hd hN hM hV X₀ hX₀ hdist W hW hind T hT

end HRS
