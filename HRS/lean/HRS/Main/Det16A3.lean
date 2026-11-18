import HRS.Main.Det22Aux1

/-!
# Example A.16, lemma L5: determinism of a zero-temperature strong solution

Like `HRS.Det22.det22_deterministic`, but pathwise uniqueness is a hypothesis (it is part of case (a) of
`SelectedFlowA1.flow`) instead of being derived from a local Lipschitz bound (which needs `d ≥ 2`), and the
initial value is only a.s. equal to a fixed configuration.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

theorem det16_deterministic {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (hβ : D.invβ = 0)
    (T : ℝ) (X₀ : Ω → Config d N) (x₀ : Config d N) (hX₀ : ∀ᵐ ω ∂P, X₀ ω = x₀)
    (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (hU : PathwiseUnique P D T X₀ W)
    (X : ℝ≥0 → Ω → Config d N) (hX : IsStrongSolution P D T X₀ W X) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀ := by
  obtain ⟨Y, hYae, hXY⟩ := hX.lift
  filter_upwards [hYae, hX.init, hX.cont, hX.no_collision, hX₀] with ω₀ h1 hi0 h3 h4 hx0
  have hX' : IsStrongSolution P D T X₀ W (fun t _ => X t ω₀) := by
    refine ⟨⟨fun t _ => Y t ω₀, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · refine Eventually.of_forall fun ω t ht => ?_
      obtain ⟨hi, he⟩ := h1 t ht
      refine ⟨hi, fun i => ?_⟩
      have := he i
      simp only [hβ, mul_zero, Real.sqrt_zero, zero_smul, add_zero] at this ⊢
      exact this
    · funext t ω
      exact congrFun (congrFun hXY t) ω₀
    · filter_upwards [hX₀] with ω hω
      rw [hω, ← hx0, ← hi0]
    · exact Eventually.of_forall fun ω => h3
    · exact fun t => measurable_const
    · exact Eventually.of_forall fun ω => h4
  exact hU X _ hX hX'

/-- The deterministic path itself: `X t ω = x t` for all `t ≤ T`, a.s. -/
theorem det16_deterministic_path {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (hβ : D.invβ = 0)
    (T : ℝ) (X₀ : Ω → Config d N) (x₀ : Config d N) (hX₀ : ∀ᵐ ω ∂P, X₀ ω = x₀)
    (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (hU : PathwiseUnique P D T X₀ W)
    (X : ℝ≥0 → Ω → Config d N) (hX : IsStrongSolution P D T X₀ W X) :
    ∃ x : ℝ≥0 → Config d N, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = x t := by
  obtain ⟨ω₀, h⟩ := (det16_deterministic P D hβ T X₀ x₀ hX₀ W hU X hX).exists
  exact ⟨fun t => X t ω₀, h⟩

end HRS.Main.Det16
