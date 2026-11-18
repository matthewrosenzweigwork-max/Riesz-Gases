import HRS.MP.SelfSimP4Final
import HRS.MP.SelfSimP5Spec

/-!
# S.A.28, packet P5: interface between the P4 level machinery and the chamber (7), (8)

`fisherCptW` is `fisherInfoW` with test fields that are smooth with compact support but not necessarily supported away from
collisions (the class of `ss5_fish`).  `p4_core_cpt` is the time-independent level chain of `SelfSimP4Spec.ss_P4_entropy_free_proof`
(lemmas (5)-(8) of P4) for such test fields; the statement below is the interface, proved in `SelfSimP5Core*.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Core

variable {d : ℕ}

/-- `fisherInfoW` with all smooth compactly supported test fields. -/
def fisherCptW {N : ℕ} (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) : ℝ≥0∞ :=
  ⨆ (ζ : EucConfig d N → EucConfig d N) (_ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ),
    ENNReal.ofReal (∫ X : EucConfig d N,
      (-2 * configDivW ζ X - 2 * fderiv ℝ (fun Z : EucConfig d N => Real.log (G Z)) X (ζ X) -
        ∑ i, ‖ζ X i‖ ^ 2) ∂P)

/-- Level `ε` dissipation inequality for a time-independent potential with Lipschitz drift and quadratic confinement
(the chain (5)-(8) of P4 with `V' = 0`, with `fisherCptW`). -/
theorem p4_core_cpt {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : EucConfig d N → ℝ} {b : EucConfig d N → EucConfig d N}
    {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp (fun _ => V) (fun _ => b) T)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ (fun _ => b) T μ)
    (hfin : gibbsEntropyW (p4GibbsOf θ V) (μ 0) < ⊤) :
    ∀ t ∈ Icc (0 : ℝ) T,
      gibbsEntropyW (p4GibbsOf θ V) (μ t) +
        ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, fisherCptW (p4GibbsOf θ V) (μ r) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (p4GibbsOf θ V) (μ 0) := by
  sorry

end HRS.MP.SelfSimP5Core
