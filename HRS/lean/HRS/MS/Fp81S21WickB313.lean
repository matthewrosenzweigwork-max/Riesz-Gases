import HRS.MS.Fp81S21WickB312

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- All classes with a finite-rank representation form a submodule, without
requiring smoothness of the factors. -/
def fp81s21_wickB313_representableSubmodule {d : ℕ} (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) where
  carrier := {k | fp81s21_wickB37_representable μ k}
  zero_mem' := by
    exact fp81s21_wickB37_span_representable μ ⟨0, (fp81s21_wickB32_finiteRankSubmodule μ).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    have hn := fp81s21_wickB37_representable_smul hy (-1)
    simpa using fp81s21_wickB37_representable_sub hx hn
  smul_mem' := by
    intro a x hx
    exact fp81s21_wickB37_representable_smul hx a

/-- Symmetric finite-rank classes with arbitrary L² factors. -/
def fp81s21_wickB313_symmetricRepresentable {d : ℕ} (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
  fp81s21_wickB313_representableSubmodule μ ⊓ fp81s21_wickB32_symmetricSubmodule μ

theorem fp81s21_wickB313_span_le {d : ℕ} (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : fp81s21_wickB32_finiteRankSubmodule μ ≤
      fp81s21_wickB313_symmetricRepresentable μ := by
  intro x hx
  exact ⟨fp81s21_wickB37_span_representable μ ⟨x, hx⟩,
    fp81s21_wickB32_finiteRank_le_symmetric μ hx⟩

#print axioms fp81s21_wickB313_span_le

end HRS.Fp81.S21
end
