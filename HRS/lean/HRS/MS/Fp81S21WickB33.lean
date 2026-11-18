import HRS.MS.Fp81S21WickB32

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- Every symmetrizer-fixed product L² class belongs to the closure of the
smooth symmetric finite-rank span. -/
theorem fp81s21_wickB33_symmetric_mem_closure {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ))
    (hfixed : fp81s21_wickB23_symmetrize μ k = k) :
    k ∈ closure (fp81s21_wickB32_finiteRankSubmodule μ : Set (Lp ℝ 2 (μ.prod μ))) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨m, c, u, hdata, happ, hrep⟩ :=
    fp81s21_wickB24_symmetric_range_dense μ k hfixed (ε / 2) (by linarith)
  have hu : ∀ i, MemLp (u i) 2 μ := fun i =>
    (hdata.smooth i).continuous.memLp_of_hasCompactSupport (hdata.compactSupport i)
  obtain ⟨q, e, M, he, hdecomp, hk, hkae, hkint⟩ :=
    fp81s21_wickG_kernel_orthonormal_coordinates u hu c
  let kr := hk.toLp (fp81s21_wickG_finite_rank_kernel u c)
  refine ⟨kr, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨m, c, u, hdata, hk, rfl⟩
  · have hdist : dist kr k ≤ ε / 2 := by
      rw [← hrep, Lp.dist_edist, Lp.edist_toLp_toLp]
      have hfinite : eLpNorm
          ((fp81s21_wickG_finite_rank_kernel u c) -
            fp81s21_wickB24_symmRepresentative k) 2 (μ.prod μ) ≠ ⊤ :=
        (hk.sub (fp81s21_wickB24_symmRepresentative_memLp k)).eLpNorm_ne_top
      have hb := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 happ
      simpa [ENNReal.toReal_ofReal (show 0 ≤ ε / 2 by linarith)] using hb
    rw [dist_comm]
    linarith

#print axioms fp81s21_wickB33_symmetric_mem_closure

end HRS.Fp81.S21
end
