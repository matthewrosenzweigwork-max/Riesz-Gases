import HRS.MS.S21T4ProdL

/-! S13: smooth test functions are dense in L² of any Borel probability measure, including atomic μ. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T3
open HRS.Whole
variable {d : ℕ}

/-- The exact smooth-test class of R26-T3.S13 is dense in L²(μ),
without a positive density or non-atomicity assumption. -/
theorem s21t4_test_dense (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    Dense {f : Lp ℝ 2 μ | ∃ g : Euc d → ℝ, f =ᵐ[μ] g ∧ IsR2Test g} := by
  have hbase : Dense
      {f : Lp ℝ 2 μ | ∃ g : Euc d → ℝ,
        f =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := (2 : ℝ≥0∞)) (by norm_num)
  have heq : {f : Lp ℝ 2 μ | ∃ g : Euc d → ℝ,
        f =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} =
      {f : Lp ℝ 2 μ | ∃ g : Euc d → ℝ, f =ᵐ[μ] g ∧ IsR2Test g} := by
    ext f
    constructor
    · rintro ⟨g, hg, hc, hs⟩
      exact ⟨g, hg, ⟨hs, hc⟩⟩
    · rintro ⟨g, hg, ⟨hs, hc⟩⟩
      exact ⟨g, hg, hc, hs⟩
  rwa [heq] at hbase

end HRS.MS.R26T3
