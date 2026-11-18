import HRS.MS.Fp81S21WickB3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The smooth symmetric finite-rank product kernels, viewed as L² classes. -/
def fp81s21_wickB32_generators {d : ℕ} (μ : Measure (Euc d)) :
    Set (Lp ℝ 2 (μ.prod μ)) :=
  {k | ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
    IsR2FiniteRankData c u ∧
    ∃ hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ),
      k = hk.toLp (fp81s21_wickG_finite_rank_kernel u c)}

/-- The algebraic span of smooth symmetric finite-rank kernels. -/
def fp81s21_wickB32_finiteRankSubmodule {d : ℕ} (μ : Measure (Euc d)) :
    Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
  Submodule.span ℝ (fp81s21_wickB32_generators μ)

/-- The fixed-point subspace of product-kernel symmetrization. -/
def fp81s21_wickB32_symmetricSubmodule {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
  (fp81s21_wickB23_symmetrize μ - ContinuousLinearMap.id ℝ _).toLinearMap.ker

/-- Each smooth symmetric finite-rank generator, and hence its span, is fixed
by the symmetrizer. -/
theorem fp81s21_wickB32_finiteRank_le_symmetric {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    fp81s21_wickB32_finiteRankSubmodule μ ≤
      fp81s21_wickB32_symmetricSubmodule μ := by
  apply Submodule.span_le.mpr
  rintro k ⟨m, c, u, hdata, hk, rfl⟩
  have hu : ∀ i, MemLp (u i) 2 μ := fun i =>
    (hdata.smooth i).continuous.memLp_of_hasCompactSupport (hdata.compactSupport i)
  have hc : fp81s21_wickB23_symmCoeff c = c := by
    funext i j
    dsimp [fp81s21_wickB23_symmCoeff]
    rw [hdata.symm i j]
    ring
  have hs : MemLp (fun z : Euc d × Euc d =>
      r2FiniteRankKernel (fp81s21_wickB23_symmCoeff c) u z.1 z.2)
      2 (μ.prod μ) := by simpa [hc] using hk
  have heq := fp81s21_wickB23_symmetrize_finite_rank u hu c hk hs
  have hfixed : fp81s21_wickB23_symmetrize μ
      (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) =
      hk.toLp (fp81s21_wickG_finite_rank_kernel u c) := by
    simpa only [hc] using heq
  change fp81s21_wickB23_symmetrize μ
      (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) -
      hk.toLp (fp81s21_wickG_finite_rank_kernel u c) = 0
  rw [hfixed, sub_self]

#print axioms fp81s21_wickB32_finiteRank_le_symmetric

end HRS.Fp81.S21
end
