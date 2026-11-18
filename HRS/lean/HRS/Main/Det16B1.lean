import HRS.Main.Linearization

/-! # det16b L11: convergence of Dirac masses (Example A.16 assembly) -/

open Filter Topology MeasureTheory
open scoped ENNReal

namespace HRS.Main.Det16

/-- `det16b_dirac_conv`: if `ξ_N → ξl` in a topological space with measurable points, then the Dirac
masses `δ_{ξ_N}` converge in law to `δ_{ξl}`. -/
theorem det16b_dirac_conv {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (ξ : ℕ → E) (ξl : E) (h : Tendsto ξ atTop (𝓝 ξl)) :
    ConvergesInLaw (fun N => Measure.dirac (ξ N)) (Measure.dirac ξl) := by
  intro f
  simp only [integral_dirac]
  exact (f.continuous.tendsto ξl).comp h

/-- Sup-norm form: a bound `‖ξ_N - ξl‖ ≤ ε_N` with `ε_N → 0` gives `ξ_N → ξl`, hence convergence in law
of the Dirac masses (any normed group with measurable points). -/
theorem det16b_dirac_conv_of_norm_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (ξ : ℕ → E) (ξl : E) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hb : ∀ᶠ N in atTop, ‖ξ N - ξl‖ ≤ ε N) :
    ConvergesInLaw (fun N => Measure.dirac (ξ N)) (Measure.dirac ξl) := by
  refine det16b_dirac_conv ξ ξl ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hε

end HRS.Main.Det16
