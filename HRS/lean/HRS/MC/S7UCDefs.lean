import HRS.MC.S7FCDefs
import HRS.MC.S7FCH4C

/-!
# Vocabulary of the `uniform_chaos` (row 7.9) packet statements (sorry-free)

Sorry-free definitions used by the statements of `HRS/MC/S7UCPlan.lean` and by their proofs.  Namespace
`HRS.MC.Sec7.UCPlan`.

* `UCField R r P' η B`: the three properties of the half-line quadratic Gaussian field `B` that
  `uniform_chaos` asks for, in the form the window estimates consume them: joint measurability, the Wick centring
  `IsWickQuadraticField` for a.e. `t ≥ 0`, and, for every horizon `T > 0` and every window start `a ≥ 0`, a.s. membership of
  `t ↦ B (a + t) ω` in `L²([0,T]; E_r)`.  (The last conjunct is exactly the hypothesis that makes `toL2 r T (B (a + ·))`
  honest, i.e. not the junk value `0`, on the limit side of the pair.)

The statements also use the vocabulary of `S7FCDefs.lean` (`FRKernel`, `fcPartAt`, `fcGaussAt`, `FCKernelData`) and, for
the finite-rank pair transport, `S7FCH4_Y`, `S7FCH4_iota`, `S7FCH4_Lp` (`S7FCH4B.lean`, `S7FCH4C.lean`; sorry-free).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.UCPlan

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

/-- The half-line quadratic Gaussian field `B` of `uniform_chaos`: jointly measurable, Wick-centred for a.e. `t ≥ 0`, and a.s.
in `L²([0,T];E_r)` along every window `a + ·`, `a ≥ 0`, `T > 0`. -/
def UCField (R : Regime d) (r : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (η B : ℝ → Ω' → NegSobolev d r) : Prop :=
  Measurable (Function.uncurry B) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
    ∀ T : ℝ, 0 < T → ∀ a : ℝ, 0 ≤ a →
      ∀ᵐ ω ∂P', MemLp (fun t => B (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T))

end HRS.MC.Sec7.UCPlan

end
