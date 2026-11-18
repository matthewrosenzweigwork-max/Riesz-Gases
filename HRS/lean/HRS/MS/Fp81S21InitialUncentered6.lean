import HRS.MS.Fp81S21InitialUncentered5

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)

/-- Fubini symmetrization for an odd vector kernel. The second term in the commutator
integral becomes the first term after swapping the two variables. -/
theorem fp81s21_integrated_odd_kernel_symmetrization
    {d : ℕ} {μ : Measure (Euc d)} [IsFiniteMeasure μ]
    {G : Euc d → Euc d → Euc d}
    {v : Euc d → Euc d}
    (hGodd : ∀ x y, G y x = -G x y)
    (hleft : Integrable
      (fun p : Euc d × Euc d => ⟪G p.1 p.2, v p.1⟫) (μ.prod μ))
    (hright : Integrable
      (fun p : Euc d × Euc d => ⟪G p.1 p.2, v p.2⟫) (μ.prod μ)) :
    ∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.1 - v p.2⟫ ∂(μ.prod μ) =
      2 * ∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.1⟫ ∂(μ.prod μ) := by
  let B : Euc d × Euc d → ℝ := fun p => ⟪G p.1 p.2, v p.2⟫
  have hswap :
      ∫ p : Euc d × Euc d, B p ∂(μ.prod μ) =
        ∫ p : Euc d × Euc d, B p.swap ∂(μ.prod μ) := by
    rw [integral_prod_swap]
  have hswapNeg :
      ∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.2⟫ ∂(μ.prod μ) =
        -∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.1⟫ ∂(μ.prod μ) := by
    calc
      _ = ∫ p : Euc d × Euc d, ⟪G p.2 p.1, v p.1⟫ ∂(μ.prod μ) := by
        simpa [B] using hswap
      _ = ∫ p : Euc d × Euc d, -⟪G p.1 p.2, v p.1⟫ ∂(μ.prod μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [hGodd p.1 p.2, inner_neg_left]
      _ = _ := by rw [integral_neg]
  have hsub :
      ∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.1 - v p.2⟫ ∂(μ.prod μ) =
        ∫ p : Euc d × Euc d,
          (⟪G p.1 p.2, v p.1⟫ - ⟪G p.1 p.2, v p.2⟫) ∂(μ.prod μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change ⟪G p.1 p.2, v p.1 - v p.2⟫ = _
    rw [inner_sub_right]
  calc
    _ = _ := hsub
    _ = (∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.1⟫ ∂(μ.prod μ)) -
        ∫ p : Euc d × Euc d, ⟪G p.1 p.2, v p.2⟫ ∂(μ.prod μ) := integral_sub hleft hright
    _ = _ := by rw [hswapNeg]; ring

#print axioms fp81s21_integrated_odd_kernel_symmetrization

end HRS.Fp81.S21

end
